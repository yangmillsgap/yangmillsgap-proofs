export const placeholders = {
  domain: "yangmillsgap.com",
  githubOrg: "yangmillsgap",
  siteName: "yangmillsgap"
};

export function deskOrigin() {
  const theOverride = process.env.MG_DESK;
  if (theOverride != undefined && theOverride.length > 0) {
    return theOverride.replace(/\/+$/, "");
  }
  return "https://" + placeholders.domain;
}

export function siteOrigin() {
  return "https://" + placeholders.domain;
}

export function upstreamRepo() {
  const theOverride = process.env.MG_UPSTREAM;
  if (theOverride != undefined && theOverride.length > 0) {
    return theOverride;
  }
  return placeholders.githubOrg + "/" + placeholders.siteName + "-proofs";
}

export function isConfigured() {
  const theAll = placeholders.domain + placeholders.githubOrg + placeholders.siteName;
  return theAll.indexOf("{{") == -1;
}

export function isDeskConfigured() {
  const theOrigin = deskOrigin();
  return theOrigin.indexOf("{{") == -1;
}
