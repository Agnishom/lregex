Verified and Efficient Matching of Regular Expressions with Lookaround
===

This repository contains the Coq formalization accompanying the paper "Verified and Efficient Matching of Regular Expressions with Lookaround" by Agnishom Chattopadhyay, Angela W. Li and Konstantinos Mamouras, to be presented at CPP 2025.

> **Abstract**
>
> Regular expressions can be extended with lookarounds for contextual matching. This paper discusses a Coq formalization of the theory of regular expressions with lookarounds. We provide an efficient and purely functional algorithm for matching expressions with lookarounds and verify its correctness. The algorithm runs in time linear in both the size of the regular expression as well as the input string. Our experimental results provide empirical support to our complexity analysis. To the best of our knowledge, this is the first formalization of a linear-time matching algorithm for regular expressions with lookarounds.

This builds upon [prior work](https://dl.acm.org/doi/10.1145/3632934) published in POPL 2024.

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

# Correspondence with the [Preprint](preprint.pdf)

| Location in Draft | Concept | Coq File | Coq Definition |
| --- | --- | --- | --- |
| Page 2, Definition 1 | Lookaround Syntax | `LRegex.v` | `LRegex` |
| Page 2, Figure 1 | Lookaround Semantics | `LRegex.v` | `match_regex` |
| Page 3, Definition 3 | Regex Equivalence | `Equations.v` | `regex_eq` |
| | Regex Containment | `Equations.v` | `regex_leq` |
| Page 4, Section 3.1 | Oracle Strings | `ORegex.v` | `ostring` |
| Page 4, Definition 4 | ORegex Syntax | `ORegex.v` | `ORegex` |
|  | ORegex Semantics | `ORegex.v` | `match_o_regex` |
| Page 5, Definition 6 | Maximal Lookarounds | `Abstraction.v` | `maximal_lookarounds` |
| | Arity | `Abstraction.v` | `arity` |
| Page 5, Definition 7 | Abstraction | `Abstraction.v` | `abstract` |
| Page 5, Definition 9 | Tape | `Abstraction.v` | `is_lookaround_tape` |
| | Tape | `LRegex.v` | `is_tape` |
| | Oracle Valuations | `Abstraction.v` | `is_oval` |
| Page 6, Lemma 11 | Connection between LRegex and ORegex | `Abstraction.v` | `oracle_compose` |
| Page 7, Definition 12 | Synax of Marked Expressions | `OMatcher.v` | `MRegex` |
| | Semantics of Marked Expressions | `OMatcher.v` | `match_mregex` |
| | Stripping Marks | `OMatcher.v` | `strip` |
| Page 8, Figure 2 | Operations on Marked Expressions | `OMatcher.v` | `nullableWith`, `finalWith`, `followWith`, `read`, `shiftWith`, `initMarkWith`|
| Page 7, Lemma 14, Part 1 | Behavior of `nullable` | `OMatcher.v` | `nullable` | `nullableWith_iff` |
| Part 2 | Behavior of `final` | `OMatcher.v` | `finalWith_fw` |
| Part 3 | Behavior of `final` | `OMatcher.v` | `finalWith_bw` |
| Page 7, Lemma 16, Part 1 | Behavior of `read` | `OMatcher.v` | `read_subset` |
| Part 2 | Behavior of `read` | `OMatcher.v` | `read_fw` |
| Part 3 | Behavior of `read` | `OMatcher.v` | `read_bw` |
| Part 4 | Behavior of `read` | `OMatcher.v` | `read_no_spurious` |
| Page 7 | Relation between `follow` and `init` and `shift` | `OMatcher.v` | `followWith_false`, `followWith_true` |
| Page 8, Lemma 18, Part 1 | Behavior of `init` | `OMatcher.v` | `initMarkWith_superset` | 
| Part 2 | Behavior of `init` | `OMatcher.v` | `stripLang_in_initMarkWith` |
| Part 3 | Behavior of `init` | `OMatcher.v` | `initMarkWith_bw` |
| Part 4 | Behavior of `shift` | `OMatcher.v` | `shiftWith_fw` |
| Part 5 | Behavior of `shift` | `OMatcher.v` | `shiftWith_bw` |
| Page 9 | Syntax of Marked Regexes with Caching | `CMatcher.v` | `CMRegex` |
| | Uncache | `CMatcher.v` | `uncache` |
| | Smart Constructors for CMRegex | `CMatcher.v` | `mkEpsilon`, `mkCharClass`, `mkQueryPos`, `mkQueryNeg`, `mkConcat`, `mkUnion`, `mkStar` |
| | Synchronization between Valuation and CMRegex | `CMatcher.v` | `synced` |
| Page 9, Figure 3 | Operations on CMRegex | `CMatcher.v` | `syncVal`, `cFollow`, `cRead` |
| Page 9, Lemma 20, Part 1 | Behavior of `sync` | `CMatcher.v` | `synced_syncVal`, `syncVal_unCache` |
| Part 2 | Behavior of `cRead` | `CMatcher.v` | `synced_cRead` |
| Part 3 | Behavior of `cRead` | `CMatcher.v` | `cRead_unCache` |
| Part 4 | Behavior of `cFollow` | `CMatcher.v` | `synced_unCache_followWith` |
| Page 10, Definition 21 | oMatch | `CMatcher.v` | `cScanMatch` |
| Page 10, Theorem 22 | Correctness of oMatch | `CMatcher.v` | `cScanMatch_tape` |
| Page 10, Section 5.1 | Reversal of LRegex | `Reverse.v` | `reverse` |
| | Reversal of ORegex | `OReverse.v` | `oreverse` |
| Page 10, Lemma 24, Part 1 | Property of Reversal (LRegex) | `Reverse.v` | `reverse_match` |
| Part 2 | Property of Reversal (ORegex) | `OReverse.v` | `oreverse_match_iff` |
| Part 3 | Computing Tapes for Lookahead | `Abstraction.v` | `lookahead_tape_is_tape` |
| Part 4 | Reverse of Abstracted Regex | `Layerwise.v` | `is_otape_oval_rev` |
| Page 11, Figure 3 | The Matching Algorithm | `Layerwise.v` | `llmatch`, `scanMatch`, `absEvalAux`, `absEval` |
| Page 11, Lemma 25 | Behavior of `evalAux` | `Layerwise.v` | `absEvalAux_spec` |
| Page 11, Theorem 26 | Correctness of `match` | `Layerwise.v` | `scanMatch_correct` |
| | Correctness of Leftmost Longest Match | `Layerwise.v` | `llmatch_correct` |