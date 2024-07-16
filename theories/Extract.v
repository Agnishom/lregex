Require Import Layerwise.

Require Import Extraction.
Require Import Coq.extraction.ExtrHaskellNatInt.
Require Import Coq.extraction.ExtrHaskellBasic.
Extraction Language Haskell.

Require Import Coq.Lists.List.

Extract Inlined Constant rev => "Prelude.reverse".

Set Extraction Output Directory "../haskell/src".
Extraction "Extracted.hs" Layerwise.scanMatch Layerwise.llmatch.