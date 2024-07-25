# Checking Proofs

To check the proofs, you need Coq 8.19. Once you have Coq installed, you can run `make` from the `theories/` directory. This will run the proof scripts, and extract the code to `haskell/src/Extracted.hs`.

Alternatively, you can check the proofs inside a container. From the main directory, run `docker build --progress=plain -t lregex .`

# Proof Structure

The syntax and semantics of regular expressions with lookarounds are defined in `LRegex.v` (see `LRegex` and `match_regex`). The function `llmatch` in `Layerwise.v` finds the leftmost longest match, and this is proven correct in `llmatch_correct`.

The files contain detailed comments. A brief overview of the files is as follows:

- `ListLemmas.v`: lemmas about lists that can be used in conjunction with those in `Coq.Lists.List`.
- `LRegex.v`: syntax and semantics of regular expressions with lookarounds, the definition of `is_tape`
- `Equations.v`: Equations (using `≡`) and inequalities (using `⊑`) on regular expressions. Includes Kleene Axioms, and identities involving lookarounds.
- `ORegex.v`: defintion of strings with oracle valuations (`ostring`), syntax and semantics of regular expressions with oracle queries.
- `Reverse.v`, `OReverse.v`: reversal of regular expressions and oracle regular expressions.
- `Abstraction.v`: connection between regular expressions and oracle regular expressions.
- `OMatcher.v`: matching algorithm for oracle regular expressions on ostrings.
- `CMatcher.v`: an optimization of the same matching algorithm that avoids recomputation using caching
- `Layerwise.v`: the main algorithm for matching regular expressions with lookarounds on strings, and finding the leftmost longest match.
