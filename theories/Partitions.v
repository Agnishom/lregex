Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Lia.

Require Import ListLemmas.

Section Partition.

Record Partition : Type := mkPartition
    { pBegin : nat;
      pBlocks : list nat;
    }.

Definition pLength (p : Partition) : nat :=
  pBegin p + fold_right plus 0 (pBlocks p).

Definition pEnd (p : Partition) : nat :=
  pBegin p + length (pBlocks p).

Definition has_no_empty_blocks (p : Partition) : Prop :=
  forall b, In b (pBlocks p) -> b > 0.

End Partition.