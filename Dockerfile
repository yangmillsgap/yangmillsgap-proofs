# Pinned checker image: Lean toolchain, Mathlib cache and the vendored Yang–Mills
# public files, prebuilt. CI runs untrusted step files inside this image with no
# network, a memory cap and a time limit (see .github/workflows/check.yml).
#
# Build:   docker build -t massgap-check:v4.32.0 .
# Publish: .github/workflows/image.yml pushes ghcr.io/<owner>/<repo>-check:<toolchain tag>

FROM node:22.23.1-bookworm-slim

ARG CHECKER_UID=1001
ARG ELAN_COMMIT=227caca133724d5516bee25c2aeb3e609478f2d8

RUN apt-get update \
 && apt-get install -y --no-install-recommends git curl ca-certificates xz-utils \
 && rm -rf /var/lib/apt/lists/* \
 && useradd --create-home --uid "${CHECKER_UID}" checker \
 && mkdir -p /opt/proofs \
 && chown checker:checker /opt/proofs

USER checker
ENV ELAN_HOME=/home/checker/.elan
ENV PATH=/home/checker/.elan/bin:${PATH}
WORKDIR /opt/proofs

COPY --chown=checker:checker lean-toolchain ./
RUN curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_COMMIT}/elan-init.sh" -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --no-modify-path --default-toolchain none \
 && rm /tmp/elan-init.sh \
 && elan toolchain install "$(cat lean-toolchain)" \
 && elan default "$(cat lean-toolchain)"

COPY --chown=checker:checker lakefile.toml lake-manifest.json MassGap.lean ./
COPY --chown=checker:checker vendor vendor
COPY --chown=checker:checker MassGap/Defs.lean MassGap/Defs.lean
RUN lake exe cache get \
 && lake build YMPublic MassGap.Defs

COPY --chown=checker:checker MassGap/Statement.lean MassGap/Statement.lean
RUN lake build MassGap.Statement

COPY --chown=checker:checker CheckLemma.lean ./
COPY --chown=checker:checker tools tools
RUN lake env lean CheckLemma.lean

CMD ["bash"]
