(**

In the file [OMatcher.v], an algorithm for matching Oracle Regular Expressions [ORegex] in Oracle Strings [ostring] is formalized. In this file, we formalize some optimizations on that algorithm. The C in [CMatcher.v] stands for Caching. The main optimization is that we cache the results of the functions [finalWith] and [nullableWith], so that computing them is done in tandem with building the value itself and they can be looked up later in costant time.

1. The main type used in this file is [CMRegex]. It is defined in a mutually inductive manner with the type [CMRe]. 
  - The type [CMRegex] is a wrapper around [CMRe] and contains two boolean fields. These fields can be accessed using the functions [cRe], [cNullable] and [cFinal] which are defined for convenience.
  - The function [unCache] converts a [CMRegex] to a [MRegex] by removing the caching information.
  - The relation [synced : valuation -> CMRegex -> Prop] asserts that the [CMRegex] is synchronized with respect to the given valuation. This happens when the fields [cNullable] and [cFinal] contain the correct values. This is established in the lemmas [synced_unCache_nullableWith] and [synced_unCache_finalWith].
2. The functions [mkEpsilon], [mkCharClass], [mkQueryPos], [mkQueryNeg], [mkConcat], [mkUnion] and [mkStar] behave like 'smart constructors'. This is to say that they set the fields [cNullable] and [cFinal] correctly based on the input [CMRegex]es.
  - The correctness of these 'smart constructors' are established in [synced_mkEpsilon], [synced_mkCharClass], [synced_mkQueryPos], [synced_mkQueryNeg], [synced_mkConcat], [synced_mkUnion] and [synced_mkStar].
  - The function [syncVal] is used to synchronize a [CMRegex] with respect to a given valuation. The correctness of this function is established in [synced_syncVal].
3. The functions [cRead], [cFollow] and [toCMarked] are counterparts of the functions [read], [followWith] and [toMarked] respectively. The correctness of these functions are established in [cRead_unCache], [synced_unCache_followWith] and [toCMarked_unCache].
4. The function [cConsume] is the counterpart of the function [consume]. The correctness of this function is established in [cConsume_empty], [cConsume_singleton] and [cConsume_step].
  - The function [cScanMatch : ORegex -> ostring -> list bool] is the counterpart of the function [oscanMatcher]. The correctness of this function is established in [cScanMatch_tape].


*)

Require Import Lia.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.

Import ListNotations.
Import Bool.


Require Import ListLemmas.
Require Import ORegex.
Require Import OMatcher.

Section CMRegex.

Context {A : Type}.

Inductive CMRegex : Type :=
    | MkCMRegex : bool -> bool -> CMRe -> CMRegex
with CMRe : Type :=
    | CMEpsilon : CMRe
    | CMCharClass : (A -> bool) -> CMRe
    | CMQueryPos : nat -> CMRe
    | CMQueryNeg : nat -> CMRe
    | CMConcat : CMRegex -> CMRegex -> CMRe
    | CMUnion : CMRegex -> CMRegex -> CMRe
    | CMStar : CMRegex -> CMRe
.

Definition cNullable (r : CMRegex) : bool :=
match r with
    | MkCMRegex b _ _ => b
end.

Definition cFinal (r : CMRegex) : bool :=
match r with
    | MkCMRegex _ b _ => b
end.

Definition cRe (r : CMRegex) : CMRe :=
match r with
    | MkCMRegex _ _ re => re
end.

Definition mkEpsilon : CMRegex :=
  MkCMRegex true false CMEpsilon.

Definition mkCharClass (mark : bool) (f : A -> bool) : CMRegex :=
  MkCMRegex false mark (CMCharClass f).

Definition mkQueryPos (b : bool) (n : nat) : CMRegex :=
  MkCMRegex b false (CMQueryPos n).

Definition mkQueryNeg (b : bool) (n : nat) : CMRegex :=
  MkCMRegex b false (CMQueryNeg n).

Definition mkConcat (r1 r2 : CMRegex) : CMRegex :=
  MkCMRegex 
    (cNullable r1 && cNullable r2) 
    ((cFinal r1 && cNullable r2) || cFinal r2)
    (CMConcat r1 r2).

Definition mkUnion (r1 r2 : CMRegex) : CMRegex :=
  MkCMRegex 
    (cNullable r1 || cNullable r2) 
    (cFinal r1 || cFinal r2)
    (CMUnion r1 r2).

Definition mkStar (r : CMRegex) : CMRegex :=
  MkCMRegex true (cFinal r) (CMStar r).

Fixpoint synced (v : valuation) (r : CMRegex) : Prop :=
    match cRe r with
    | CMEpsilon => cFinal r = false /\ cNullable r = true
    | CMCharClass _ => cNullable r = false
    | CMQueryPos n => 
        cFinal r = false 
     /\ cNullable r = match nth_error v n with
                        | Some true => true
                        | _ => false
                      end
    | CMQueryNeg n =>
        cFinal r = false
     /\ cNullable r = match nth_error v n with
                        | Some false => true
                        | _ => false
                      end
    | CMConcat r1 r2 =>
        cFinal r = ((cFinal r1 && cNullable r2) || cFinal r2)
     /\ cNullable r = (cNullable r1 && cNullable r2)
     /\ synced v r1
     /\ synced v r2
    | CMUnion r1 r2 =>
        cFinal r = (cFinal r1 || cFinal r2)
     /\ cNullable r = (cNullable r1 || cNullable r2)
     /\ synced v r1
     /\ synced v r2
    | CMStar r1 =>
        cFinal r = cFinal r1
     /\ cNullable r = true
     /\ synced v r1
    end.

Fixpoint unCache (r : CMRegex) : MRegex :=
  match cRe r with
  | CMEpsilon => MEpsilon
  | CMCharClass f => MCharClass (cFinal r) f
  | CMQueryPos n => MQueryPos n
  | CMQueryNeg n => MQueryNeg n
  | CMConcat r1 r2 => MConcat (unCache r1) (unCache r2)
  | CMUnion r1 r2 => MUnion (unCache r1) (unCache r2)
  | CMStar r1 => MStar (unCache r1)
  end.

Fixpoint syncVal (v : valuation) (r : CMRegex) : CMRegex :=
  match cRe r with
  | CMEpsilon => mkEpsilon
  | CMCharClass f => mkCharClass (cFinal r) f
  | CMQueryPos n => mkQueryPos (match nth_error v n with
                                  | Some true => true
                                  | _ => false
                                end) n
  | CMQueryNeg n => mkQueryNeg (match nth_error v n with
                                  | Some false => true
                                  | _ => false
                                end) n
  | CMConcat r1 r2 => mkConcat (syncVal v r1) (syncVal v r2)
  | CMUnion r1 r2 => mkUnion (syncVal v r1) (syncVal v r2)
  | CMStar r1 => mkStar (syncVal v r1)
  end.

Fixpoint cRead (a : A) (r : CMRegex) : CMRegex :=
  match cRe r with
  | CMEpsilon => r
  | CMCharClass f => mkCharClass (cFinal r && f a) f
  | CMQueryPos n => r
  | CMQueryNeg n => r
  | CMConcat r1 r2 => mkConcat (cRead a r1) (cRead a r2)
  | CMUnion r1 r2 => mkUnion (cRead a r1) (cRead a r2)
  | CMStar r1 => mkStar (cRead a r1)
  end.

Fixpoint cFollow (b : bool) (r : CMRegex) : CMRegex :=
  match cRe r with
  | CMEpsilon => mkEpsilon
  | CMCharClass f => mkCharClass b f
  | CMQueryPos n => r
  | CMQueryNeg n => r
  | CMConcat r1 r2 => 
    let b1 := cFinal r1 || (b && cNullable r1) in
    mkConcat (cFollow b r1) (cFollow b1 r2)
  | CMUnion r1 r2 => mkUnion (cFollow b r1) (cFollow b r2)
  | CMStar r1 => mkStar (cFollow (b || cFinal r1) r1)
  end.

Fixpoint toCMarked (or : @ORegex A) : CMRegex :=
  match or with
  | OEpsilon => mkEpsilon
  | OCharClass f => mkCharClass false f
  | OQueryPos n => mkQueryPos false n
  | OQueryNeg n => mkQueryNeg false n
  | OConcat or1 or2 => mkConcat (toCMarked or1) (toCMarked or2)
  | OUnion or1 or2 => mkUnion (toCMarked or1) (toCMarked or2)
  | OStar or1 => mkStar (toCMarked or1)
  end.

(* when using, we want |w| = |o| *)
Fixpoint cConsumeAux (cmr : CMRegex) (w : list A) (o : list valuation) : CMRegex :=
  match w, o with
  | [], [] => cmr
  | [], _ :: _ => mkEpsilon (* shouldn't arise! *)
  | _ :: _, [] => mkEpsilon (* shouldn't arise! *)
  | a0 :: w', v1 :: o' => 
    let cmrNew := cFollow false cmr in
    let cmrNew' := cRead a0 cmrNew in
    let cmrNew'' := syncVal v1 cmrNew' in
    cConsumeAux cmrNew'' w' o'
  end.


Definition cConsume (or : ORegex) (os : @ostring A) : CMRegex :=
  let cmr := toCMarked or in
  match os with
  | (_, []) => cmr (* shouldn't arise! *)
  | ([], [o0]) => syncVal o0 cmr
  | (_ , _ :: []) => cmr (* shouldn't arise! *)
  | (a0 :: w', o0 :: o1 :: o') =>
    let cmr0   := cFollow true (syncVal o0 cmr) in
    let cmr0'  := cRead a0 cmr0 in
    let cmr0'' := syncVal o1 cmr0' in
    cConsumeAux cmr0'' w' o'
  | (_, _ :: _ :: _) => cmr (* shouldn't arise! *)
  end.

(* when using, we want |w| = |o| *)
Fixpoint cScanMatchAux (cmr : CMRegex) (w : list A) (o : list valuation) : list bool :=
  let b := cFinal cmr in
  match w, o with
  | [], [] => [b]
  | [], _ :: _ => [b] (* shouldn't arise! *)
  | _ :: _, [] => [b] (* shouldn't arise! *)
  | a0 :: w', v1 :: o' => 
    let cmrNew := cFollow false cmr in
    let cmrNew' := cRead a0 cmrNew in
    let cmrNew'' := syncVal v1 cmrNew' in
    b :: cScanMatchAux cmrNew'' w' o'
  end.

Definition cScanMatch (or : ORegex) (os : @ostring A) : list bool :=
  let cmr := toCMarked or in
  match os with
  | (_, []) => [] (* shouldn't arise! *)
  | ([], [o0]) => [cNullable (syncVal o0 cmr)]
  | (_ , _ :: []) => [] (* shouldn't arise! *)
  | (a0 :: w', o0 :: o1 :: o') =>
    let b0 := cNullable (syncVal o0 cmr) in
    let cmr0   := cFollow true (syncVal o0 cmr) in
    let cmr0'  := cRead a0 cmr0 in
    let cmr0'' := syncVal o1 cmr0' in
    b0 :: cScanMatchAux cmr0'' w' o'
  | (_, _ :: _ :: _) => [] (* shouldn't arise! *)
  end.

Hint Unfold synced : regex.

Lemma synced_mkEpsilon :
  forall v : valuation,
    synced v mkEpsilon.
Proof.
    intros. simpl. auto.
Qed.

Lemma synced_mkCharClass :
  forall (v : valuation) (mark : bool) (f : A -> bool),
    synced v (mkCharClass mark f).
Proof.
    intros. simpl. auto.
Qed.

Lemma synced_mkQueryPos :
  forall (v : valuation) (n : nat) (b : bool),
    b = match nth_error v n with
        | Some true => true
        | _ => false
    end
    <-> synced v (mkQueryPos b n).
Proof.
    intros. simpl. tauto.
Qed.

Lemma synced_mkQueryNeg :
  forall (v : valuation) (n : nat) (b : bool),
    b = match nth_error v n with
        | Some false => true
        | _ => false
    end
    <-> synced v (mkQueryNeg b n).
Proof.
    intros. simpl. tauto.
Qed.

Lemma synced_mkConcat :
  forall (v : valuation) (r1 r2 : CMRegex),
  synced v r1 /\ synced v r2 <-> 
  synced v (mkConcat r1 r2). 
Proof.
    intros. simpl. tauto.
Qed.

Lemma synced_mkUnion :
  forall (v : valuation) (r1 r2 : CMRegex),
  synced v r1 /\ synced v r2 <-> 
  synced v (mkUnion r1 r2).
Proof.
    intros. simpl. tauto.
Qed.

Lemma synced_mkStar :
  forall (v : valuation) (r : CMRegex),
  synced v r <-> 
  synced v (mkStar r).
Proof.
    intros. simpl. tauto.
Qed.

Hint Resolve synced_mkEpsilon : regex.
Hint Resolve synced_mkCharClass : regex.
Hint Resolve synced_mkQueryPos : regex.
Hint Resolve synced_mkQueryNeg : regex.
Hint Resolve synced_mkConcat : regex.
Hint Resolve synced_mkUnion : regex.
Hint Resolve synced_mkStar : regex.



Fixpoint CMRegex_ind_2 (P : CMRe -> Prop) 
  (HEps: P CMEpsilon)
  (HCharClass : (forall f : A -> bool, P (CMCharClass f)))
  (HQueryPos : (forall n : nat, P (CMQueryPos n)))
  (HQueryNeg : (forall n : nat, P (CMQueryNeg n)))
  (HConcat : forall r1 r2 : CMRe, 
           P r1 
        -> P r2 
        -> forall n1 f1 n2 f2, 
        P (CMConcat (MkCMRegex n1 f1 r1) (MkCMRegex n2 f2 r2)))
  (HUnion : forall r1 r2 : CMRe, 
           P r1 
        -> P r2 
        -> forall n1 f1 n2 f2,
        P (CMUnion (MkCMRegex n1 f1 r1) (MkCMRegex n2 f2 r2)))
  (HStar : (forall r : CMRe, 
           P r 
        -> forall n f, P (CMStar (MkCMRegex n f r))))
  (r : CMRe) : P r :=
  let inductor := CMRegex_ind_2 P HEps HCharClass HQueryPos HQueryNeg HConcat HUnion HStar in
  match r with
    | CMEpsilon => HEps
    | CMCharClass f => HCharClass f
    | CMQueryPos n => HQueryPos n
    | CMQueryNeg n => HQueryNeg n
    | CMConcat (MkCMRegex n1 f1 r1) (MkCMRegex n2 f2 r2) => HConcat r1 r2 (inductor r1) (inductor r2) n1 f1 n2 f2
    | CMUnion (MkCMRegex n1 f1 r1) (MkCMRegex n2 f2 r2) => HUnion r1 r2 (inductor r1) (inductor r2) n1 f1 n2 f2
    | CMStar (MkCMRegex n f r) => HStar r (inductor r) n f
    end.


Lemma synced_unCache_nullableWith (v : valuation) (r : CMRegex) :
    synced v r 
    -> cNullable r = nullableWith v (unCache r).
Proof.
  destruct r as [cNull cFin re]. revert cNull cFin.
  induction re using CMRegex_ind_2;
    try (simpl in *; tauto).
  (* Concat *)
  { intros cNull cFin.
  remember (MkCMRegex n1 f1 re1) as r1.
  remember (MkCMRegex n2 f2 re2) as r2.
  simpl synced. intro Hsynced.
  destruct Hsynced as [_ [Hnull [Hs1 Hs2]]].
  simpl unCache. simpl nullableWith.
  simpl cNullable. subst cNull.
  subst r1 r2.
  specialize (IHre1 n1 f1 Hs1).
  specialize (IHre2 n2 f2 Hs2).
  congruence.
  }
  (* Union *)
  { intros cNull cFin.
  remember (MkCMRegex n1 f1 re1) as r1.
  remember (MkCMRegex n2 f2 re2) as r2.
  simpl synced. intro Hsynced.
  destruct Hsynced as [_ [Hnull [Hs1 Hs2]]].
  simpl unCache. simpl nullableWith.
  simpl cNullable. subst cNull.
  subst r1 r2.
  specialize (IHre1 n1 f1 Hs1).
  specialize (IHre2 n2 f2 Hs2).
  congruence.
  }
Qed.

Lemma synced_unCache_finalWith (v : valuation) (r : CMRegex) :
    synced v r 
    -> cFinal r = finalWith v (unCache r).
Proof.
    destruct r as [cNull cFin re]. revert cNull cFin.
    induction re using CMRegex_ind_2;
        try (simpl in *; tauto).
    (* Concat *)
    { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl synced. intro Hsynced.
    destruct Hsynced as [Hfin [_ [Hs1 Hs2]]].
    simpl unCache. simpl finalWith.
    simpl cFinal.
    pose proof (synced_unCache_nullableWith _ _ Hs2) as Hnull.
    subst cFin.
    subst r1 r2.
    specialize (IHre1 n1 f1 Hs1).
    specialize (IHre2 n2 f2 Hs2).
    congruence.
    }
    (* Union *)
    { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl synced. intro Hsynced.
    destruct Hsynced as [Hfin [_ [Hs1 Hs2]]].
    simpl unCache. simpl finalWith.
    simpl cFinal. subst cFin.
    subst r1 r2.
    specialize (IHre1 n1 f1 Hs1).
    specialize (IHre2 n2 f2 Hs2).
    congruence.
    }
    (* Star *)
    { intros cNull cFin.
    remember (MkCMRegex n f re) as r.
    simpl synced. intro Hsynced.
    destruct Hsynced as [Hfin [Hnull Hs]].
    simpl unCache. simpl finalWith.
    simpl cFinal. subst cFin.
    subst r.
    specialize (IHre n f Hs).
    congruence.
    }
Qed.
    


Lemma synced_syncVal (v : valuation) (r : CMRegex) :
    synced v (syncVal v r).
Proof.
   destruct r as [cNull cFin re]. revert cNull cFin.
   induction re using CMRegex_ind_2;
    try (simpl in *; tauto).
   (* Concat *)
   { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl syncVal.
    apply synced_mkConcat.
    specialize (IHre1 n1 f1).
    specialize (IHre2 n2 f2).
    rewrite <- Heqr1 in IHre1.
    rewrite <- Heqr2 in IHre2.
    auto.
    }
    (* Union *)
    { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl syncVal.
    apply synced_mkUnion.
    specialize (IHre1 n1 f1).
    specialize (IHre2 n2 f2).
    rewrite <- Heqr1 in IHre1.
    rewrite <- Heqr2 in IHre2.
    auto.
    }
    (* Star *)
    { intros cNull cFin.
    remember (MkCMRegex n f re) as r.
    simpl syncVal.
    rewrite <- synced_mkStar.
    specialize (IHre n f).
    rewrite <- Heqr in IHre.
    auto.
    }
Qed.

Lemma syncVal_unCache (r : CMRegex) (v : valuation) :
  unCache (syncVal v r) = unCache r.
Proof.
  destruct r as [cNull cFin re]. revert cNull cFin.
  induction re using CMRegex_ind_2;
    try (simpl in *; tauto).
  (* Concat *) { 
    intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl syncVal.
    simpl unCache.
    subst r1 r2.
    specialize (IHre1 n1 f1).
    specialize (IHre2 n2 f2).
    rewrite IHre1.
    rewrite IHre2. 
    auto.
  }
  (* Union *) { 
    intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl syncVal.
    simpl unCache.
    subst r1 r2.
    specialize (IHre1 n1 f1).
    specialize (IHre2 n2 f2).
    rewrite IHre1.
    rewrite IHre2. 
    auto.
  }
  (* Star *) { 
    intros cNull cFin.
    remember (MkCMRegex n f re) as r.
    simpl syncVal.
    simpl unCache.
    subst r.
    specialize (IHre n f).
    rewrite IHre.
    auto.
  }
Qed.


Lemma synced_cRead (v : valuation) (r : CMRegex) (a : A) :
    synced v r -> synced v (cRead a r).
Proof.
  destruct r as [cNull cFin re]. revert cNull cFin.
  induction re using CMRegex_ind_2;
    try (simpl in *; tauto).
  (* Concat *)
  { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    intros Hsynced.
    destruct Hsynced as [_ [_ [Hs1 Hs2]]].
    simpl cRead.
    apply synced_mkConcat.
    subst r1 r2.
    specialize (IHre1 n1 f1 Hs1).
    specialize (IHre2 n2 f2 Hs2).
    auto.
  }
  (* Union *)
  { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    intros Hsynced.
    destruct Hsynced as [_ [_ [Hs1 Hs2]]].
    simpl cRead.
    apply synced_mkUnion.
    subst r1 r2.
    specialize (IHre1 n1 f1 Hs1).
    specialize (IHre2 n2 f2 Hs2).
    auto.
  }
  (* Star *)
  { intros cNull cFin.
    remember (MkCMRegex n f re) as r.
    intros Hsynced.
    destruct Hsynced as [_ [_ Hs]].
    simpl cRead.
    rewrite <- synced_mkStar.
    subst r.
    now specialize (IHre n f Hs).
  }
Qed. 

Lemma cRead_unCache (a : A) (r : CMRegex) :
    unCache (cRead a r) = read a (unCache r).
Proof.
  destruct r as [cNull cFin re]. revert cNull cFin.
  induction re using CMRegex_ind_2;
      try (simpl in *; tauto).
  (* Concat *){ 
    intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl cRead.
    simpl unCache.
    subst r1 r2.
    specialize (IHre1 n1 f1).
    specialize (IHre2 n2 f2).
    rewrite IHre1.
    rewrite IHre2. 
    auto.
  }
  (* Union *){ 
    intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    simpl cRead.
    simpl unCache.
    subst r1 r2.
    specialize (IHre1 n1 f1).
    specialize (IHre2 n2 f2).
    rewrite IHre1.
    rewrite IHre2. 
    auto.
  }
  (* Star *) {
    intros cNull cFin.
    remember (MkCMRegex n f re) as r.
    simpl cRead.
    simpl unCache.
    subst r.
    specialize (IHre n f).
    rewrite IHre.
    auto.
  }
Qed.

Lemma synced_unCache_followWith (v : valuation) (r : CMRegex) (b : bool) :
  synced v r
  -> unCache (cFollow b r) = followWith b v (unCache r).
Proof.
  destruct r as [cNull cFin re]. revert cNull cFin b v.
  induction re using CMRegex_ind_2;
    try (simpl in *; tauto).
  (* Concat *)
  { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    intros b v Hsynced.
    destruct Hsynced as [Hfinal [Hnull [Hs1 Hs2]]].
    simpl in Hfinal.
    simpl cFollow. simpl unCache. simpl followWith.
    pose proof (synced_unCache_nullableWith _ _ Hs1) as Hnull1.
    pose proof (synced_unCache_finalWith _ _ Hs1) as Hfinal1.
    subst r2.
    specialize (IHre2 n2 f2 (cFinal r1 || b && cNullable r1) v Hs2). 
    rewrite IHre2.
    subst r1.
    specialize (IHre1 n1 f1 b v Hs1). rewrite IHre1.
    rewrite Hfinal1. rewrite Hnull1.
    reflexivity.
  }
  (* Union *)
  { intros cNull cFin.
    remember (MkCMRegex n1 f1 re1) as r1.
    remember (MkCMRegex n2 f2 re2) as r2.
    intros b v Hsynced.
    destruct Hsynced as [_ [_ [Hs1 Hs2]]].
    simpl cFollow. simpl unCache. simpl followWith.
    subst r1 r2.
    specialize (IHre1 n1 f1 b v Hs1). rewrite IHre1.
    specialize (IHre2 n2 f2 b v Hs2). rewrite IHre2.
    reflexivity.
  }
  (* Star *)
  { intros cNull cFin.
    remember (MkCMRegex n f re) as r.
    intros b v Hsynced.
    destruct Hsynced as [Hfinal [_ Hs]].
    pose proof (synced_unCache_finalWith _ _ Hs) as Hfinal1.
    simpl cFollow. simpl unCache. simpl followWith.
    rewrite Hfinal1.
    specialize (IHre n f (b || finalWith v (unCache r)) v ltac:(now subst)).
    subst.
    rewrite IHre. 
    reflexivity.
  }
Qed.



Lemma toCMarked_unCache (or : @ORegex A) :
  unCache (toCMarked or) = toMarked or.
Proof.
  induction or; simpl; auto.
  all: congruence.
Qed.



Lemma cConsumeAux_snoc (cmr : CMRegex) (w : list A) (o : list valuation) 
  (a' : A) (v' : valuation) :
  length w = length o
  -> cConsumeAux cmr (w ++ [a']) (o ++ [v']) = 
      syncVal v' (cRead a' (cFollow false (cConsumeAux cmr w o))).
Proof.
  remember (length w) as n eqn:Hn.
  revert n cmr w o v' a' Hn.
  induction n.
  - intros cmr w o v' a' Hlen Heq.
    destruct w as [ | w0 w']. 2 : { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. 2 : { simpl in Heq. lia. }
    auto.
  - intros mr w o v' a' Hlen Heq.
    destruct w as [ | w0 w']. { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. { simpl in Heq. lia. }
    simpl in Hlen. simpl in Heq.
    simpl. rewrite IHn. auto.
    lia. lia.
Qed.

Lemma cConsume_snoc (or : ORegex) (w : list A) (o : list valuation) 
  (a' : A) (v' : valuation) :
  outer_length_wf (w, o)
  -> olength (w, o) > 0
  -> cConsume or (w ++ [a'], o ++ [v']) =
      syncVal v' (cRead a' (cFollow false (cConsume or (w, o)))).
Proof.
  intros Hwf Hlen.
  unfold outer_length_wf in Hwf.
  unfold olength in Hlen. simpl in * |-.
  destruct o as [ | o0 o']. { simpl in Hwf. lia. }
  destruct w as [ | a0 w']. { simpl in Hlen. lia. }
  destruct o' as [ | o1 o'']. { simpl in Hwf. lia. }
  simpl app.
  simpl. apply cConsumeAux_snoc.
  simpl in Hwf. lia.
Qed.



Lemma cConsume_empty (or : ORegex) (v0 : valuation) : 
  unCache (cConsume or ([], [v0])) = toMarked or
  /\ synced v0 (cConsume or ([], [v0])).
Proof.
  simpl.
  rewrite syncVal_unCache.
  rewrite toCMarked_unCache.
  split; [ auto | ].
  apply synced_syncVal.
Qed.

Lemma cConsume_singleton (or : ORegex) (a0 : A) (v0 v1 : valuation) :
  unCache (cConsume or ([a0], [v0 ; v1])) = read a0 (consume or ([], [v0]))
  /\ synced v1 (cConsume or ([a0], [v0 ; v1])).
Proof.
  simpl.
  remember (syncVal v0 (toCMarked or)) as cr0.
  assert (synced v0 cr0). {
    subst. apply synced_syncVal.  
  }
  remember (cFollow true cr0) as cr1.
  assert (unCache cr1 = followWith true v0 (unCache cr0)). {
    subst cr1. apply synced_unCache_followWith. assumption. 
  }
  remember (cRead a0 cr1) as cr2.
  assert (unCache cr2 = read a0 (unCache cr1)). {
    subst cr2. apply cRead_unCache.
  }
  remember (syncVal v1 cr2) as cr3.
  assert (synced v1 cr3). {
    subst cr3. apply synced_syncVal.
  }
  split; [ | auto].
  subst cr3.
  rewrite syncVal_unCache.
  subst cr2.
  rewrite cRead_unCache.
  rewrite H0.
  f_equal. f_equal.
  subst cr0.
  rewrite syncVal_unCache.
  rewrite toCMarked_unCache.
  reflexivity.
Qed.

Lemma cConsume_step (or : ORegex) (w : list A) (o : list valuation) 
  (a a' : A) (v v' : valuation) :
  outer_length_wf (w, o)
  -> unCache (cConsume or (w ++ [a], o ++ [v])) = read a (consume or (w, o))
  -> synced v (cConsume or (w ++ [a], o ++ [v]))
  -> unCache (cConsume or ((w ++ [a]) ++ [a'], (o ++ [v]) ++ [v'])) = read a' (consume or (w ++ [a], o ++ [v]))
  /\ synced v' (cConsume or ((w ++ [a]) ++ [a'], (o ++ [v]) ++ [v'])).
Proof.
  intros Hwf Hconsume Hsynced.
  rewrite cConsume_snoc.
  rewrite consume_snoc; [ | auto].
  split.
  - rewrite syncVal_unCache. rewrite cRead_unCache.
    erewrite synced_unCache_followWith.
    f_equal. f_equal. auto. auto. 
  - apply synced_syncVal.
  - unfold outer_length_wf in *. simpl in Hwf |- *.
  rewrite app_length. rewrite app_length.  
  simpl. auto.
  -  unfold olength. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma cConsume_nonempty (or : ORegex) (w : list A) (o : list valuation) 
  (a : A) (v : valuation) :
  outer_length_wf (w, o)
  -> unCache (cConsume or (w ++ [a], o ++ [v])) = read a (consume or (w, o))
  /\ synced v (cConsume or (w ++ [a], o ++ [v])).
Proof.
  revert o v a.
  induction w using rev_ind. {
    intros ? ? ? Hwf.
    unfold outer_length_wf in Hwf.
    simpl in Hwf.
    destruct o as [ | o0 o' ]. { simpl in Hwf. lia. }
    destruct o' as [ | o1 o'']. 2 : { simpl in Hwf. lia. }
    simpl app.
    apply cConsume_singleton.
  }
  intros ? ? ? Hwf.
  destruct (unsnoc o) as [[o' oX]|] eqn:E.
  2 : { rewrite unsnoc_None in E. subst o.
    unfold outer_length_wf in Hwf. simpl in Hwf.
    rewrite app_length in Hwf. simpl in Hwf. lia.
  }
  rewrite unsnoc_Some in E.
  subst o.
  assert (outer_length_wf (w, o')). {
    unfold outer_length_wf in *. simpl in *.
    repeat rewrite app_length in Hwf.
    simpl in Hwf. lia.
  }
  specialize (IHw o' oX x H) as [IH1 IH2].
  apply cConsume_step; auto.
Qed.

Lemma cmembership_empty (or : ORegex) (v0 : valuation):
  cNullable (cConsume or ([], [v0])) = true
  <-> match_oregex or ([], [v0]).
Proof.
  simpl.
  rewrite synced_unCache_nullableWith with (v := v0).
  - rewrite syncVal_unCache.
  rewrite toCMarked_unCache.
  rewrite nullableWith_iff.
  now rewrite toMarked_strip.
  - apply synced_syncVal.
Qed.  

Lemma cmembership_nonempty (or : ORegex) (w : list A) (o : list valuation) 
  (a : A) (v : valuation) :
  outer_length_wf (w, o)
  -> cFinal (cConsume or (w ++ [a], o ++ [v])) = true
  <-> match_oregex or (w ++ [a], o ++ [v]).
Proof.
  intros Hwf.
  pose proof (cConsume_nonempty or w o a v Hwf) as [Hconsume Hsynced].
  rewrite synced_unCache_finalWith with (v := v); [ | auto].
  rewrite Hconsume.
  replace w with (fst (w, o)) by auto.
  replace o with (snd (w, o)) at 2 4 by auto.
  now apply membership_nonempty.
Qed.



Lemma cScanMatchAux_hd_error (cmr : CMRegex) (w : list A) (o : list valuation) :
  hd_error (cScanMatchAux cmr w o) = Some (cFinal cmr).
Proof.
  destruct w; destruct o; auto.
Qed.

Lemma cScanMatchAux_cons (cmr : CMRegex) (w : list A) (o : list valuation) (a0 : A) (v0 : valuation) :
  cScanMatchAux cmr (a0 :: w) (v0 :: o) = 
    cFinal cmr :: cScanMatchAux (syncVal v0 (cRead a0 (cFollow false cmr))) w o.
Proof.
  reflexivity.
Qed.

Lemma cScanMatchAux_length (cmr : CMRegex) (w : list A) (o : list valuation) :
  length w = length o
  -> length (cScanMatchAux cmr w o) = S (length w).
Proof.
  revert cmr o.
  induction w.
  - intros cmr o Hlen. destruct o. 2 : { simpl in Hlen. lia. }
    simpl. reflexivity.
  - intros cmr o Hlen. destruct o. 1 : { simpl in Hlen. lia. }
    simpl in Hlen.
    simpl. rewrite IHw; lia.
Qed.

Lemma cScanMatch_length (or : ORegex) (os : @ostring A) :
  outer_length_wf os
  -> length (cScanMatch or os) = S (olength os).
Proof.
  intros Hwf.
  unfold outer_length_wf in Hwf.
  destruct os as [w o].
  unfold olength. simpl fst.
  destruct o as [ | o0 o']. 1 : { simpl in Hwf. lia. }
  destruct o' as [ | o1 o'']. {
    destruct w as [ | a0 w']. 2 : { simpl in Hwf. lia. }
    auto.
  }
  destruct w as [ | a0 w']. 1 : { simpl in Hwf. lia. }
  simpl. rewrite cScanMatchAux_length; auto.
  simpl in Hwf. lia.
Qed.

Lemma cScanMatchAux_tl (or : ORegex) (w w' : list A) (o o' : list valuation) 
  (a' : A) (v' : valuation) :
    outer_length_wf (w, o)
    -> olength (w, o) > 0
    -> tl (cScanMatchAux (cConsume or (w, o)) (a' :: w' ) (v' :: o')) = 
      cScanMatchAux (cConsume or (w ++ [a'], o ++ [v'])) w' o'.
Proof.
  intros Hwf Hlen. rewrite cConsume_snoc; auto.
Qed.

Lemma cScanMatchAux_skipn (or : ORegex) (w w': list A) (o o': list valuation) 
   (n : nat) :
    outer_length_wf (w, o)
    -> length w' = length o'
    -> olength (w, o) > 0
    -> n <= length w'
    -> skipn n (cScanMatchAux (cConsume or (w, o)) w' o') =
        cScanMatchAux (cConsume or (w ++ firstn n w', o ++ firstn n o')) (skipn n w') (skipn n o').
Proof.
  intros Hwf Hlen Hlen'.
  revert w o w' o' Hwf Hlen Hlen'.
  induction n. {
    intros w o w' o' Hwf Hlen' Hlen Hn.
    repeat rewrite skipn_O. repeat rewrite firstn_O.
    repeat rewrite app_nil_r. reflexivity.
  } {
    intros w o w' o' Hwf Hlen' Hlen Hn.
    destruct w' as [ | a' w'']. {
      simpl in Hn. lia.
    }
    destruct o' as [ | v' o'']. {
      simpl in Hlen'. lia.
    }
    simpl skipn at 2 3.
    simpl firstn.
    rewrite cScanMatchAux_cons.
    rewrite skipn_cons.
    rewrite <- cConsume_snoc; auto.
    rewrite IHn; auto.
    f_equal. f_equal. f_equal.
    - rewrite <- app_assoc. reflexivity.
    - rewrite <- app_assoc. reflexivity.
    - unfold outer_length_wf in Hwf |- *. simpl in Hwf |- *.
      repeat rewrite app_length. simpl. lia.
    - unfold olength in Hlen |- *. simpl in Hlen |- *.
      rewrite app_length. simpl. lia.
    - simpl in Hn. lia.
  }
Qed.

Lemma cScanMatch_nth_error_S (or : ORegex) (w : list A) (o : list valuation) (n : nat) :
  outer_length_wf (w, o)
  -> n > 0
  -> n <= length w
  -> nth_error (cScanMatch or (w, o)) n = 
      Some (cFinal (cConsume or (ofirstn n (w, o)))).
Proof.
  intros Hwf Hn1 Hn.
  (* n != 0 *)
  destruct n. lia.
  (* when n = 1 *)
  destruct n. {
    destruct o as [ | o0 o']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    destruct o' as [ | o1 o'']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    destruct w as [ | a0 w']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    unfold ofirstn. simpl firstn.
    simpl cScanMatch.
    remember (cScanMatchAux _ _).
    remember 0 as zero.
    replace 1 with (S zero) by auto.
    simpl nth_error. subst zero.
    rewrite <- hd_error_nth_error.
    subst l. rewrite cScanMatchAux_hd_error.
    reflexivity.
  }
  (* when n >= 2 *){
    destruct o as [ | o0 o']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    destruct o' as [ | o1 o'']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    destruct w as [ | a0 w']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    destruct w' as [ | a1 w'']. 1 : { simpl in Hn. lia. }
    destruct o'' as [ | o2 o''']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    unfold ofirstn. simpl firstn.
    simpl cScanMatch.
    simpl nth_error.
    remember (syncVal _ _) as cr2.
    replace cr2 with (cConsume or ([a0; a1], [o0; o1; o2])) by auto.
    clear Heqcr2.
    replace ((a0 :: a1 :: firstn n w'', o0 :: o1 :: o2 :: firstn n o'''))
      with (([a0; a1] ++ firstn n w'', [o0; o1; o2] ++ firstn n o''')) by auto.
    replace n with (0 + n) at 1 by auto.
    rewrite nth_error_skipn. rewrite <- hd_error_nth_error.
    rewrite cScanMatchAux_skipn.
    - rewrite cScanMatchAux_hd_error. reflexivity.
    - unfold outer_length_wf. reflexivity.
    - unfold outer_length_wf in Hwf. simpl in Hwf. lia.
    - unfold olength. simpl. lia.
    - simpl in Hn. lia.  
  }
Qed.

Lemma cScanMatch_nth_error_O (or : ORegex) (w : list A) (o : list valuation) :
  outer_length_wf (w, o)
  -> nth_error (cScanMatch or (w, o)) 0 = 
      Some (cNullable (cConsume or (ofirstn 0 (w, o)))).
Proof.
  intros Hwf.
  destruct o as [ | o0 o']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
  unfold ofirstn. simpl firstn.
  rewrite <- hd_error_nth_error.
  destruct w; destruct o'; auto.
  all : unfold outer_length_wf in Hwf; simpl in Hwf; lia.
Qed.

Lemma cScanMatch_tape (r : ORegex) (os : @ostring A) :
  outer_length_wf os
  -> (length (cScanMatch r os) = olength os + 1) /\
    forall i,
      i <= olength os ->
      (nth_error (cScanMatch r os) i = Some true <-> match_oregex r (ofirstn i os)) /\
      (nth_error (cScanMatch r os) i = Some false <-> ~ match_oregex r (ofirstn i os)).
Proof.
  intros Hwf.
  split.
  { rewrite cScanMatch_length. lia. assumption. }
  intros i Hlen.
  destruct i.
  (* when i is 0 *) {
    destruct os as [w o].
    rewrite cScanMatch_nth_error_O; auto.
    destruct o as [ | o0 o']. 1 : { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    unfold ofirstn. simpl.
    pose proof (cConsume_empty r o0) as [_ Hsynced].
    pose proof (cmembership_empty r o0) as Hmembership.
    clear Hsynced.
    repeat split; intros.
    - inversion H; tauto.
    - rewrite <- Hmembership in H. simpl in H. now rewrite H.
    - inversion H. intros M. apply Hmembership in M.
      simpl in M. rewrite H1 in M. discriminate.
    - simpl in Hmembership. remember (cNullable _) as b.
      destruct b; [ tauto | auto].
  }
  (* when i > 0 *) {
    destruct os as [w o].
    rewrite cScanMatch_nth_error_S; auto. 2: lia.
    unfold outer_length_wf in Hwf. unfold olength in Hlen.
    simpl in Hlen, Hwf.
    replace (ofirstn (S i) (w, o)) with ((firstn (S i) w, firstn (S (S i)) o)) by auto.
    destruct (unsnoc (firstn (S i) w)) as [[w' a] | ] eqn:Ew.
    2 : {
      rewrite unsnoc_None in Ew.
      apply f_equal with (f := @length A) in Ew.
      rewrite firstn_length in Ew.
      simpl length in Ew. lia.
    }
    rewrite unsnoc_Some in Ew. rewrite Ew.
    destruct (unsnoc (firstn (S (S i)) o)) as [[o' v] | ] eqn:Eo.
    2 : {
      rewrite unsnoc_None in Eo.
      apply f_equal with (f := @length valuation) in Eo.
      rewrite firstn_length in Eo.
      simpl length in Eo. lia.
    }
    rewrite unsnoc_Some in Eo. rewrite Eo.
    assert (outer_length_wf (w', o')). {
      unfold outer_length_wf. simpl.
      apply f_equal with (f := @length A) in Ew.
      rewrite firstn_length in Ew.
      apply f_equal with (f := @length valuation) in Eo.
      rewrite firstn_length in Eo.
      rewrite app_length in Ew, Eo. simpl length in Ew, Eo.
      lia.
    }
    pose proof (cConsume_nonempty r w' o' a v H) as [_ Hsynced].
    pose proof (cmembership_nonempty r w' o' a v H) as Hmembership.
    clear Hsynced H.
    repeat split; intros.
    - inversion H; tauto.
    - rewrite <- Hmembership in H. now rewrite H.
    - remember ((cConsume r (w' ++ [a], o' ++ [v]))).
      inversion H. intros M. apply Hmembership in M.
      simpl in M. rewrite H1 in M. discriminate.
    - remember ((cConsume r (w' ++ [a], o' ++ [v]))).
      remember (cFinal _) as b.
      destruct b; [ tauto | auto].
  }
Qed.

End CMRegex.