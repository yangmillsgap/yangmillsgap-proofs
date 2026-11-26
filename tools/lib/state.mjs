import fs from "node:fs";
import path from "node:path";

export const clientKeyPattern = /^ck-[0-9a-f]{32}$/;

export function stateFileIn(statedir) {
  return path.join(statedir, "state.json");
}

export function readStateFile(statedir) {
  const theFile = stateFileIn(statedir);
  if (fs.existsSync(theFile) == false) {
    return { handle: null, leases: {} };
  }
  const theText = fs.readFileSync(theFile, "utf8");
  const theState = JSON.parse(theText);
  if (theState.leases == undefined) {
    theState.leases = {};
  }
  return theState;
}

export function writeStateFile(statedir, state) {
  fs.mkdirSync(statedir, { recursive: true });
  const theFile = stateFileIn(statedir);
  const theTemporary = theFile + ".tmp-" + process.pid;
  const theText = JSON.stringify(state, null, 2) + "\n";
  fs.writeFileSync(theTemporary, theText, { mode: 0o600 });
  fs.chmodSync(theTemporary, 0o600);
  fs.renameSync(theTemporary, theFile);
}

export function updateStateFile(statedir, change) {
  const theFresh = readStateFile(statedir);
  change(theFresh);
  writeStateFile(statedir, theFresh);
  return theFresh;
}

export function clientKeyOf(state) {
  if (state.client_keys == undefined || state.handle == null) {
    return null;
  }
  const theKey = state.client_keys[state.handle];
  if (typeof theKey != "string" || clientKeyPattern.test(theKey) == false) {
    return null;
  }
  return theKey;
}

export function firstLeaseForHandle(state, handle) {
  if (state.joined_told == undefined) {
    return true;
  }
  return state.joined_told[handle] != true;
}

export function leaseChange(leaseid, fields) {
  const theNames = Object.keys(fields);
  function change(state) {
    const theLease = state.leases[leaseid];
    if (theLease == undefined) {
      return;
    }
    for (let n = 0; n < theNames.length; n++) {
      theLease[theNames[n]] = fields[theNames[n]];
    }
  }
  return change;
}
