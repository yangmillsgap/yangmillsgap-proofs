import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const libDir = path.dirname(fileURLToPath(import.meta.url));
export const schemaDir = path.join(libDir, "..", "schemas");

export const schemaFiles = {
  deskNextQuery: "desk/next-query.schema.json",
  deskNextResponse: "desk/next-response.schema.json",
  deskBeatQuery: "desk/beat-query.schema.json",
  deskBeatResponse: "desk/beat-response.schema.json",
  deskReleaseRequest: "desk/release-request.schema.json",
  deskReleaseResponse: "desk/release-response.schema.json",
  deskStepResponse: "desk/step-response.schema.json",
  deskError: "desk/error.schema.json",
  checkerHookPayload: "hook/checker-payload.schema.json",
  checkerHookHeaders: "hook/checker-headers.schema.json",
  checkerHookResponse: "hook/checker-response.schema.json"
};

const fileCache = new Map();
const patternCache = new Map();

function loadFile(file) {
  const theCached = fileCache.get(file);
  if (theCached != undefined) {
    return theCached;
  }
  const theText = fs.readFileSync(file, "utf8");
  const theSchema = JSON.parse(theText);
  fileCache.set(file, theSchema);
  return theSchema;
}

function patternOf(source) {
  const theCached = patternCache.get(source);
  if (theCached != undefined) {
    return theCached;
  }
  const thePattern = new RegExp(source, "u");
  patternCache.set(source, thePattern);
  return thePattern;
}

function resolveRef(ref, file) {
  const theHash = ref.indexOf("#");
  const theFilePart = theHash == -1 ? ref : ref.slice(0, theHash);
  const thePointer = theHash == -1 ? "" : ref.slice(theHash + 1);
  const theFile = theFilePart.length == 0 ? file : path.resolve(path.dirname(file), theFilePart);
  let theNode = loadFile(theFile);
  const theSteps = thePointer.split("/");
  for (let n = 0; n < theSteps.length; n++) {
    const theStep = theSteps[n];
    if (theStep.length == 0) {
      continue;
    }
    theNode = theNode[theStep.replace(/~1/g, "/").replace(/~0/g, "~")];
    if (theNode == undefined) {
      throw new Error("the schema reference " + ref + " does not resolve");
    }
  }
  return { schema: theNode, file: theFile };
}

function typeMatches(type, value) {
  if (type == "null") {
    return value === null;
  }
  if (type == "boolean") {
    return typeof value == "boolean";
  }
  if (type == "string") {
    return typeof value == "string";
  }
  if (type == "number") {
    return typeof value == "number" && Number.isFinite(value) == true;
  }
  if (type == "integer") {
    return typeof value == "number" && Number.isInteger(value) == true;
  }
  if (type == "array") {
    return Array.isArray(value) == true;
  }
  if (type == "object") {
    return typeof value == "object" && value !== null && Array.isArray(value) == false;
  }
  return false;
}

function sameValue(left, right) {
  return JSON.stringify(left) == JSON.stringify(right);
}

function codePointLength(text) {
  return Array.from(text).length;
}

function checkNode(schema, value, file, where, errors) {
  if (schema === true) {
    return;
  }
  if (schema === false) {
    errors.push(where + " is not allowed");
    return;
  }
  if (schema.$ref != undefined) {
    const theTarget = resolveRef(schema.$ref, file);
    checkNode(theTarget.schema, value, theTarget.file, where, errors);
  }
  if (schema.type != undefined) {
    const theTypes = Array.isArray(schema.type) == true ? schema.type : [schema.type];
    let theMatched = false;
    for (let n = 0; n < theTypes.length; n++) {
      if (typeMatches(theTypes[n], value) == true) {
        theMatched = true;
      }
    }
    if (theMatched == false) {
      errors.push(where + " should be " + theTypes.join(" or "));
      return;
    }
  }
  if (schema.const !== undefined && sameValue(schema.const, value) == false) {
    errors.push(where + " should be " + JSON.stringify(schema.const));
  }
  if (schema.enum != undefined) {
    let theFound = false;
    for (let n = 0; n < schema.enum.length; n++) {
      if (sameValue(schema.enum[n], value) == true) {
        theFound = true;
      }
    }
    if (theFound == false) {
      errors.push(where + " is not one of the allowed values");
    }
  }
  if (typeof value == "string") {
    checkString(schema, value, where, errors);
  }
  if (typeof value == "number" && schema.minimum != undefined && value < schema.minimum) {
    errors.push(where + " should be at least " + schema.minimum);
  }
  if (Array.isArray(value) == true) {
    checkArray(schema, value, file, where, errors);
  } else if (typeof value == "object" && value !== null) {
    checkObject(schema, value, file, where, errors);
  }
  checkCombinators(schema, value, file, where, errors);
}

function checkString(schema, value, where, errors) {
  if (schema.minLength != undefined && codePointLength(value) < schema.minLength) {
    errors.push(where + " is too short");
  }
  if (schema.maxLength != undefined && codePointLength(value) > schema.maxLength) {
    errors.push(where + " is too long");
  }
  if (schema.pattern != undefined) {
    const thePattern = patternOf(schema.pattern);
    if (thePattern.test(value) == false) {
      errors.push(where + " does not match the expected pattern");
    }
  }
}

function checkArray(schema, value, file, where, errors) {
  if (schema.minItems != undefined && value.length < schema.minItems) {
    errors.push(where + " has too few items");
  }
  if (schema.maxItems != undefined && value.length > schema.maxItems) {
    errors.push(where + " has too many items");
  }
  let theStart = 0;
  if (schema.prefixItems != undefined) {
    for (let n = 0; n < schema.prefixItems.length && n < value.length; n++) {
      checkNode(schema.prefixItems[n], value[n], file, where + "[" + n + "]", errors);
    }
    theStart = schema.prefixItems.length;
  }
  if (schema.items != undefined) {
    for (let n = theStart; n < value.length; n++) {
      checkNode(schema.items, value[n], file, where + "[" + n + "]", errors);
    }
  }
}

function checkObject(schema, value, file, where, errors) {
  const theProperties = schema.properties ?? {};
  if (schema.required != undefined) {
    for (let n = 0; n < schema.required.length; n++) {
      const theName = schema.required[n];
      if (Object.prototype.hasOwnProperty.call(value, theName) == false) {
        errors.push(where + " is missing " + theName);
      }
    }
  }
  const theKeys = Object.keys(value);
  for (let n = 0; n < theKeys.length; n++) {
    const theKey = theKeys[n];
    const theKnown = Object.prototype.hasOwnProperty.call(theProperties, theKey);
    if (theKnown == true) {
      checkNode(theProperties[theKey], value[theKey], file, where + "." + theKey, errors);
      continue;
    }
    if (schema.additionalProperties === false) {
      errors.push(where + " has the unexpected field " + theKey.slice(0, 40));
    }
  }
}

function passes(schema, value, file, where) {
  const theErrors = [];
  checkNode(schema, value, file, where, theErrors);
  return theErrors.length == 0;
}

function checkCombinators(schema, value, file, where, errors) {
  if (schema.allOf != undefined) {
    for (let n = 0; n < schema.allOf.length; n++) {
      checkNode(schema.allOf[n], value, file, where, errors);
    }
  }
  if (schema.anyOf != undefined) {
    let theAny = false;
    for (let n = 0; n < schema.anyOf.length; n++) {
      if (passes(schema.anyOf[n], value, file, where) == true) {
        theAny = true;
      }
    }
    if (theAny == false) {
      errors.push(where + " matches none of the allowed shapes");
    }
  }
  if (schema.oneOf != undefined) {
    let theCount = 0;
    for (let n = 0; n < schema.oneOf.length; n++) {
      if (passes(schema.oneOf[n], value, file, where) == true) {
        theCount = theCount + 1;
      }
    }
    if (theCount != 1) {
      errors.push(where + " should match exactly one allowed shape, it matches " + theCount);
    }
  }
  if (schema.if != undefined) {
    const theCondition = passes(schema.if, value, file, where);
    if (theCondition == true && schema.then != undefined) {
      checkNode(schema.then, value, file, where, errors);
    }
    if (theCondition == false && schema.else != undefined) {
      checkNode(schema.else, value, file, where, errors);
    }
  }
}

export function validateAgainst(name, value) {
  const theRelative = schemaFiles[name];
  if (theRelative == undefined) {
    throw new Error("there is no schema named " + name);
  }
  const theFile = path.join(schemaDir, theRelative);
  const theSchema = loadFile(theFile);
  const theErrors = [];
  checkNode(theSchema, value, theFile, "$", theErrors);
  return theErrors;
}

export function isValidAgainst(name, value) {
  const theErrors = validateAgainst(name, value);
  return theErrors.length == 0;
}
