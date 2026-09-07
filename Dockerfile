# Keep these defaults aligned with tools/ci/pluto-baseline.env.
ARG PLUTO_IMAGE=hughshine/pluto-verif@sha256:0e15a7614af280b02ab0dc31f110c3ee3f7a1fe3ee3d1b503cc3400d87b4f4ce
ARG PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_GIT_COMMIT=73cae81a19aa74ed83370831a5300676bac0a53b
ARG PLUTO_BUGGY_GIT_REMOTE=https://github.com/verif-scop/pluto.git
ARG PLUTO_BUGGY_GIT_COMMIT=5836f8544f4226dfc87913f5d2f8684816f8f5ed
ARG PLUTO_BUGGY_ROOT=/opt/polcert/pluto-buggy

FROM ${PLUTO_IMAGE} AS buggy-pluto-builder

ARG PLUTO_BUGGY_GIT_REMOTE
ARG PLUTO_BUGGY_GIT_COMMIT

RUN apt-get update \
  && apt-get install -y libglpk-dev \
  && rm -rf /var/lib/apt/lists/* \
  && git -C /pluto remote set-url origin "${PLUTO_BUGGY_GIT_REMOTE}" \
  && git -C /pluto fetch origin "${PLUTO_BUGGY_GIT_COMMIT}" \
  && git -C /pluto checkout "${PLUTO_BUGGY_GIT_COMMIT}" \
  && cd /pluto \
  && ./configure --enable-glpk --with-glpk-prefix=/usr \
  && make clean \
  && make -j"$(nproc)"

# Export a clean checkout plus only the runtime artifacts.  Copying the build
# tree would retain hundreds of megabytes of object files in the final image.
RUN git clone --no-hardlinks /pluto /polcert-pluto-buggy \
  && git -C /polcert-pluto-buggy remote set-url origin "${PLUTO_BUGGY_GIT_REMOTE}" \
  && cp /pluto/tool/pluto /polcert-pluto-buggy/tool/pluto \
  && cp /pluto/polycc /polcert-pluto-buggy/polycc \
  && cp /pluto/inscop /polcert-pluto-buggy/inscop

FROM ${PLUTO_IMAGE} AS development-base

RUN  apt-get update \
  && apt-get install -y ca-certificates wget make m4 build-essential patch unzip git python3 libgmp-dev libglpk-dev libeigen3-dev \
  && rm -rf /var/lib/apt/lists/*

RUN wget https://github.com/ocaml/opam/releases/download/2.0.8/opam-2.0.8-x86_64-linux -O opam && \
    echo "95365a873d9e3ae6fb48e6109b5fc5df3b4e526c9d65d20652a78e263f745a35  opam" | sha256sum -c - && \
    chmod 744 opam && \
    mv opam /usr/local/bin/opam

RUN opam init -y --verbose --disable-sandboxing --bare

RUN opam switch create polcert 4.13.1

RUN opam install -y \
    coq.8.13.2 \
    dune.3.22.2 \
    glpk.0.1.8 \
    menhir.20260209 \
    ocamlfind.1.9.8 \
    stdlib-shims.0.3.0 \
    zarith.1.14

RUN echo 'eval $(opam env)' >> ~/.bashrc

# Keep the expensive, stable system and Rocq toolchain layers independent of
# the pinned Pluto revision. Feature branches can then reuse the main-branch
# BuildKit cache when only the candidate generator commit changes.
ARG PLUTO_GIT_REMOTE
ARG PLUTO_GIT_COMMIT

RUN git -C /pluto remote set-url origin "${PLUTO_GIT_REMOTE}" \
  && git -C /pluto fetch origin "${PLUTO_GIT_COMMIT}" \
  && git -C /pluto checkout "${PLUTO_GIT_COMMIT}" \
  && cd /pluto \
  && ./configure --enable-glpk --with-glpk-prefix=/usr \
  && make clean \
  && make -j"$(nproc)" \
  && make install

# BuildKit can compile this historical bug-reproduction baseline in parallel
# with the main image. It is never used by ordinary PolOpt routes.
ARG PLUTO_IMAGE
ARG PLUTO_BUGGY_GIT_REMOTE
ARG PLUTO_BUGGY_GIT_COMMIT
ARG PLUTO_BUGGY_ROOT

COPY --from=buggy-pluto-builder /polcert-pluto-buggy ${PLUTO_BUGGY_ROOT}
RUN sed -i "s|^pluto=/pluto|pluto=${PLUTO_BUGGY_ROOT}|" "${PLUTO_BUGGY_ROOT}/polycc" \
  && sed -i "s|^inscop=/pluto|inscop=${PLUTO_BUGGY_ROOT}|" "${PLUTO_BUGGY_ROOT}/polycc"

LABEL com.polcert.pluto.image="${PLUTO_IMAGE}" \
      com.polcert.pluto.remote="${PLUTO_GIT_REMOTE}" \
      com.polcert.pluto.commit="${PLUTO_GIT_COMMIT}" \
      com.polcert.pluto.buggy-remote="${PLUTO_BUGGY_GIT_REMOTE}" \
      com.polcert.pluto.buggy-commit="${PLUTO_BUGGY_GIT_COMMIT}"

ENV PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_PLUTO_IMAGE="${PLUTO_IMAGE}" \
    POLCERT_PLUTO_GIT_REMOTE="${PLUTO_GIT_REMOTE}" \
    POLCERT_PLUTO_GIT_COMMIT="${PLUTO_GIT_COMMIT}" \
    POLCERT_BUGGY_PLUTO_GIT_REMOTE="${PLUTO_BUGGY_GIT_REMOTE}" \
    POLCERT_BUGGY_PLUTO_GIT_COMMIT="${PLUTO_BUGGY_GIT_COMMIT}" \
    POLCERT_BUGGY_ROOT="${PLUTO_BUGGY_ROOT}" \
    POLCERT_BUGGY_PLUTO="${PLUTO_BUGGY_ROOT}/tool/pluto" \
    POLCERT_BUGGY_POLYCC="${PLUTO_BUGGY_ROOT}/polycc"

SHELL ["/bin/bash", "-c"]

COPY . /polcert/

WORKDIR /polcert/

RUN eval $(opam env) && ./configure x86_64-linux 

ARG POLCERT_GIT_COMMIT=unknown
LABEL org.opencontainers.image.revision="${POLCERT_GIT_COMMIT}"
ENV POLCERT_GIT_COMMIT="${POLCERT_GIT_COMMIT}"

ENTRYPOINT ["/bin/bash"]

FROM development-base AS ci

ARG CI_MAX_PROOF_JOBS=2
ARG CI_PROOF_MEMORY_MB_PER_JOB=6144
ARG CI_MAX_BUILD_JOBS=4
ARG CI_BUILD_MEMORY_MB_PER_JOB=1536

ENV CI_MAX_PROOF_JOBS="${CI_MAX_PROOF_JOBS}" \
    CI_PROOF_MEMORY_MB_PER_JOB="${CI_PROOF_MEMORY_MB_PER_JOB}" \
    CI_MAX_BUILD_JOBS="${CI_MAX_BUILD_JOBS}" \
    CI_BUILD_MEMORY_MB_PER_JOB="${CI_BUILD_MEMORY_MB_PER_JOB}"

RUN bash /polcert/tools/ci/run_ci_build.sh

FROM development-base AS development
