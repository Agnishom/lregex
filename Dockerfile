FROM alpine:latest

RUN apk update && apk add --no-cache \
    bash curl git make m4 gcc g++ ocaml \
    "coq=~8.19" "cabal=~3.10" && \
    cabal update

WORKDIR /workspace

COPY . .

RUN cd theories && \
    make && \
    cd ../haskell && \
    cabal build && \
    cabal test

ENTRYPOINT ["/bin/bash"]