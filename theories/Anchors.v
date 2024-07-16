Require Import Lia.
Require Import Coq.Arith.Wf_nat.


Require Import Coq.Lists.List.

Require Import LRegex.
Require Import Equations.

Section Anchors.

Generalizable Variables A.
Variable A : Type.


Inductive has_no_lookarounds : @LRegex A -> Prop :=
| HNLEpsilon : has_no_lookarounds Epsilon
| HNLCharClass : forall a, has_no_lookarounds (CharClass a)
| HNLConcat : forall r1 r2, has_no_lookarounds r1 -> has_no_lookarounds r2 -> has_no_lookarounds (Concat r1 r2)
| HNLUnion : forall r1 r2, has_no_lookarounds r1 -> has_no_lookarounds r2 -> has_no_lookarounds (Union r1 r2)
| HNLStar : forall r, has_no_lookarounds r -> has_no_lookarounds (Star r)
.

Definition derivative_form : Type :=
    (bool * list ((A -> bool) * @LRegex A))%type.


End Anchors.