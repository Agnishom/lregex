Require Import Lia.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.

Import ListNotations.
Import Bool.


Require Import ListLemmas.
Require Import ORegex.

Section OMatcher.

Context {A : Type}.

Inductive MRegex : Type :=
| MEpsilon : MRegex
| MCharClass : bool -> (A -> bool) -> MRegex
| MQueryPos : nat -> MRegex
| MQueryNeg : nat -> MRegex
| MConcat : MRegex -> MRegex -> MRegex
| MUnion : MRegex -> MRegex -> MRegex
| MStar : MRegex -> MRegex
.

Fixpoint strip (r : MRegex) : ORegex :=
    match r with
    | MEpsilon => OEpsilon
    | MCharClass _ f => OCharClass f
    | MQueryPos n => OQueryPos n
    | MQueryNeg n => OQueryNeg n
    | MConcat r1 r2 => OConcat (strip r1) (strip r2)
    | MUnion r1 r2 => OUnion (strip r1) (strip r2)
    | MStar r => OStar (strip r)
    end.

Fixpoint is_marked (r : MRegex) : bool :=
    match r with
    | MEpsilon => false
    | MCharClass b f => b
    | MQueryPos _ => false
    | MQueryNeg _ => false
    | MConcat r1 r2 => is_marked r1 || is_marked r2
    | MUnion r1 r2 => is_marked r1 || is_marked r2
    | MStar r => is_marked r
    end.

Inductive match_mregex : MRegex -> ostring -> Prop :=
| mmatch_charclass :
    forall (os : ostring) (a : A) (pred : A -> bool),
        olength os = 1 -> (hd_error (fst os)) = Some a -> pred a = true -> match_mregex (MCharClass true pred) os
| mmatch_union_l :
    forall (mr1 mr2 : MRegex) (os : ostring),
        match_mregex mr1 os -> match_mregex (MUnion mr1 mr2) os
| mmatch_union_r :
    forall (mr1 mr2 : MRegex) (os : ostring),
        match_mregex mr2 os -> match_mregex (MUnion mr1 mr2) os
| mmatch_concat_l :
    forall (mr1 mr2 : MRegex) (os : ostring) (n : nat),
        match_mregex mr1 (ofirstn n os) 
     -> match_oregex (strip mr2) (oskipn n os) 
     -> match_mregex (MConcat mr1 mr2) os
| mmatch_concat_r :
    forall (mr1 mr2 : MRegex) (os : ostring),
        match_mregex mr2 os -> match_mregex (MConcat mr1 mr2) os
| mmatch_star :
    forall (mr : MRegex) (os : ostring) (n : nat),
        match_mregex mr (ofirstn n os) 
     -> match_oregex (OStar (strip mr)) (oskipn n os) 
     -> match_mregex (MStar mr) os
.

Definition empty_oreg : ORegex :=
    @OCharClass A (fun _ => false).

Fixpoint markedLang (mr : MRegex) : ORegex :=
  match mr with 
  | MEpsilon => empty_oreg
  | MCharClass true f => OCharClass f
  | MCharClass false f => empty_oreg
  | MQueryPos n => empty_oreg
  | MQueryNeg n => empty_oreg
  | MUnion mr1 mr2 => OUnion (markedLang mr1) (markedLang mr2)
  | MConcat mr1 mr2 => OUnion (OConcat (markedLang mr1) (strip mr2)) (markedLang mr2)
  | MStar mr => OConcat (markedLang mr) (OStar (strip mr))
  end.

Fixpoint nullableWith (v : valuation) (mr : MRegex) : bool :=
  match mr with
  | MEpsilon => true
  | MCharClass _ _ => false
  | MQueryPos n => 
      match nth_error v n with
      | Some true => true
      | _ => false
      end
  | MQueryNeg n =>
      match nth_error v n with
      | Some false => true
      | _ => false
      end
  | MConcat mr1 mr2 => 
      nullableWith v mr1 && nullableWith v mr2
  | MUnion mr1 mr2 =>
      nullableWith v mr1 || nullableWith v mr2
  | MStar _ => true
  end.

(* this refers to the idea that if a charclass is marked, 
   then there must be some character that it matches
*)
Fixpoint no_spurious_marks (mr : MRegex) : Prop :=
  match mr with
  | MEpsilon => True
  | MCharClass true p => exists a, p a = true
  | MCharClass false _ => True
  | MQueryPos _ => True
  | MQueryNeg _ => True
  | MConcat mr1 mr2 => no_spurious_marks mr1 /\ no_spurious_marks mr2
  | MUnion mr1 mr2 => no_spurious_marks mr1 /\ no_spurious_marks mr2
  | MStar mr => no_spurious_marks mr
  end.

Fixpoint finalWith (v : valuation) (mr : MRegex) : bool :=
  match mr with
  | MEpsilon => false
  | MCharClass b p => b
  | MQueryPos _ => false
  | MQueryNeg _ => false
  | MConcat mr1 mr2 => (finalWith v mr1 && nullableWith v mr2) || finalWith v mr2
  | MUnion mr1 mr2 => finalWith v mr1 || finalWith v mr2
  | MStar mr => finalWith v mr
  end.

Fixpoint read (a : A) (mr : MRegex) : MRegex :=
  match mr with
  | MEpsilon => MEpsilon
  | MCharClass b p => MCharClass (b && p a) p
  | MQueryPos n => MQueryPos n
  | MQueryNeg n => MQueryNeg n
  | MConcat mr1 mr2 => MConcat (read a mr1) (read a mr2)
  | MUnion mr1 mr2 => MUnion (read a mr1) (read a mr2)
  | MStar mr => MStar (read a mr)
  end.

Fixpoint initMarkWith (v : valuation) (mr : MRegex) : MRegex :=
  match mr with
  | MEpsilon => MEpsilon
  | MCharClass _ p => MCharClass true p
  | MQueryPos n => MQueryPos n
  | MQueryNeg n => MQueryNeg n
  | MUnion mr1 mr2 => MUnion (initMarkWith v mr1) (initMarkWith v mr2)
  | MConcat mr1 mr2 => 
      MConcat (initMarkWith v mr1) (
        match nullableWith v mr1 with
        | true => initMarkWith v mr2
        | false => mr2
        end)
  | MStar mr => MStar (initMarkWith v mr)
  end.

Fixpoint shiftWith (v : valuation) (mr : MRegex) : MRegex :=
  match mr with
  | MEpsilon => MEpsilon
  | MCharClass b p => MCharClass false p
  | MQueryPos n => MQueryPos n
  | MQueryNeg n => MQueryNeg n
  | MUnion mr1 mr2 => MUnion (shiftWith v mr1) (shiftWith v mr2)
  | MConcat mr1 mr2 => 
      MConcat 
        (shiftWith v mr1) 
        (match finalWith v mr1 with
        | true => initMarkWith v (shiftWith v mr2)
        | false => shiftWith v mr2
        end)
  | MStar mr => MStar (
      match finalWith v mr with
      | true => initMarkWith v (shiftWith v mr)
      | false => shiftWith v mr
      end)
  end.

Fixpoint followWith (b : bool) (v : valuation) (mr : MRegex) : MRegex :=
  match mr with
  | MEpsilon => MEpsilon
  | MCharClass _ p => MCharClass b p
  | MQueryPos n => MQueryPos n
  | MQueryNeg n => MQueryNeg n
  | MUnion mr1 mr2 => MUnion (followWith b v mr1) (followWith b v mr2)
  | MConcat mr1 mr2 =>
      let b1 := (finalWith v mr1) || (b && (nullableWith v mr1)) in
      MConcat (followWith b v mr1) (followWith b1 v mr2)
  | MStar mr => MStar (followWith (b || (finalWith v mr)) v mr)
  end.

Fixpoint toMarked (or : @ORegex A) : MRegex :=
  match or with
  | OEpsilon => MEpsilon
  | OCharClass p => MCharClass false p
  | OQueryPos n => MQueryPos n
  | OQueryNeg n => MQueryNeg n
  | OUnion or1 or2 => MUnion (toMarked or1) (toMarked or2)
  | OConcat or1 or2 => MConcat (toMarked or1) (toMarked or2)
  | OStar or => MStar (toMarked or)
  end.

(* when using, we want |w| = |o| *)
Fixpoint consumeAux (mr : MRegex) (w : list A) (o : list valuation) : MRegex :=
  match (w, o) with
  | ([], []) => mr
  | ([], _ :: _) => MEpsilon (* shouldn't arise! *)
  | (_ :: _, []) => MEpsilon (* shouldn't arise! *)
  | (a0 :: w', v1 :: o') => 
      let mNew := read a0 mr in
      let mNew' := followWith false v1 mNew in
          consumeAux mNew' w' o'
  end.

Definition consume (or : ORegex) (os : @ostring A) : MRegex :=
  let mr := toMarked or in
  match os with
  | (_, []) => mr
  | (w, o0 :: o') => consumeAux (followWith true o0 mr) w o'
  end.

(* when using this function, we will make sure that |w| = |o| *)
Fixpoint matcherStatesAux (mr : MRegex) (w : list A) (o : list valuation) : list (bool * MRegex) :=
  match (w, o) with
  | ([], []) => []
  | ([], _ :: _) => [(false, MEpsilon)] (* shouldn't arise! *)
  | (_ :: _, []) => [(false, MEpsilon)] (* shouldn't arise! *)
  | (a0 :: w', v0 :: o') => 
      let mNew := read a0 mr in
      let b    := finalWith v0 mNew in
      let mNew' := followWith false v0 mNew in
      (b, mNew') :: (matcherStatesAux mNew' w' o')
  end.

(* we should use this function only when |w| + 1 = |o| *)
Definition matcherStates (or : ORegex) (os : @ostring A) : list (bool * MRegex) :=
  let mr := toMarked or in
  match os with
  | (_, []) => [(false, mr)] (* shouldn't arise! *)
  | (w, o0 :: o') =>
      let b0  := nullableWith o0 mr in
      let mr' := followWith true o0 mr in
          (b0, mr') :: (matcherStatesAux mr' w o')
  end.

Definition oscanMatcher (r : ORegex) (os : @ostring A) : list bool :=
  map fst (matcherStates r os).


Lemma mmatch_eps_never :
    forall (os : ostring),
        ~ match_mregex MEpsilon os.
Proof.
    intros ? H.
    inversion H.
Qed.

Lemma mmatch_marked_iff :
    forall (os : ostring) (pred : A -> bool),
        match_mregex (MCharClass true pred) os 
    <-> exists a, fst os = [a] /\ pred a = true.
Proof.
   intros.
   split; intros.
   - inversion H.
   subst. destruct os as [w o].
   simpl in *. destruct w; [ inversion H1 | ].
   destruct w; [ | inversion H1].
   exists a. simpl in H2.
   inversion H2. auto.
   - destruct H as [a [H1 H2]].
   destruct os as [w o]. simpl in H1; subst.
   now apply mmatch_charclass with (pred := pred) (a := a).
Qed.

Lemma mmatch_unmarked_never :
    forall (os : ostring) (pred : A -> bool),
        ~ match_mregex (MCharClass false pred) os.
Proof.
    intros ? ? H.
    inversion H.
Qed.

Lemma mmatch_querypos_never :
    forall (os : ostring) (n : nat),
        ~ match_mregex (MQueryPos n) os.
Proof.
    intros ? ? H.
    inversion H.
Qed.

Lemma mmatch_queryneg_never :
    forall (os : ostring) (n : nat),
        ~ match_mregex (MQueryNeg n) os.
Proof.
    intros ? ? H.
    inversion H.
Qed.

Lemma mmatch_union_iff :
    forall (os : ostring) (mr1 mr2 : MRegex),
        match_mregex (MUnion mr1 mr2) os
    <-> match_mregex mr1 os \/ match_mregex mr2 os.
Proof.
    intros.
    split; intros.
    - inversion H; subst; auto.
    - destruct H; [now apply mmatch_union_l | now apply mmatch_union_r].
Qed.

Lemma mmatch_concat_iff :
    forall (os : ostring) (mr1 mr2 : MRegex),
    outer_length_wf os ->
        match_mregex (MConcat mr1 mr2) os
    <-> (exists n, 0 <= n <= olength os 
                /\ match_mregex mr1 (ofirstn n os)
                /\ match_oregex (strip mr2) (oskipn n os))
    \/ match_mregex mr2 os.
Proof.
    intros ? ? ? Hwf.
    split; intros.
    - inversion H; subst.
        + left.
          assert (n <= olength os \/ n > olength os) as [Hn | Hn] by lia.
          * exists n. repeat split; auto. lia.
          * exists (olength os). repeat split.
            lia. lia. 
            ** destruct os as (w, o).
            unfold olength in *. simpl in *.
            rewrite ofirstn_all2 by auto.
            rewrite ofirstn_all2 in H2. auto.
            auto. unfold olength. simpl. lia.
            ** rewrite oskipn_all2 by auto.
            rewrite oskipn_all2 in H4. auto.
            auto. unfold olength in *.
            destruct os as (w, o); simpl in *; lia.
        + right. auto.
    - destruct H as [[n [H1 H2]] | H].
        + now apply mmatch_concat_l with (n := n).
        + now apply mmatch_concat_r.
Qed.

Lemma mmatch_star_iff : forall (os : ostring) (mr : MRegex),
    outer_length_wf os ->
        match_mregex (MStar mr) os
    <-> (exists n,
       0 <= n <= olength os
    /\ match_mregex mr (ofirstn n os) 
    /\ match_oregex (OStar (strip mr)) (oskipn n os)).
Proof.
    intros ? ? Hwf.
    split; intros.
    - inversion H; subst.
      assert (n <= olength os \/ n > olength os) as [Hn | Hn] by lia.
      + exists n. repeat split; auto. lia.
      + exists (olength os). repeat split.
        lia. lia. 
        ** destruct os as (w, o).
        unfold olength in *. simpl in *.
        rewrite ofirstn_all2 by auto.
        rewrite ofirstn_all2 in H1. auto.
        auto. unfold olength. simpl. lia.
        ** rewrite oskipn_all2 by auto.
        rewrite oskipn_all2 in H2. auto.
        auto. unfold olength in *.
        destruct os as (w, o); simpl in *; lia. 
    - destruct H as [n [H1 H2]].
    now apply mmatch_star with (n := n).
Qed.



Lemma omatch_empty_oreg_never :
    forall (os : ostring),
        ~ match_oregex empty_oreg os.
Proof.
    intros ? H.
    inversion H; subst.
    discriminate.
Qed.


Lemma mmatch_markedLang_iff :
    forall (mr : MRegex) (os : ostring),
    outer_length_wf os ->
        match_mregex mr os <-> match_oregex (markedLang mr) os.
Proof.
   induction mr; simpl.
   - pose proof mmatch_eps_never. 
     pose proof omatch_empty_oreg_never. 
     firstorder.
   - destruct b; simpl.
     + setoid_rewrite mmatch_marked_iff.
       setoid_rewrite omatch_charclass_iff.
       tauto.
     + pose proof mmatch_unmarked_never.
       pose proof omatch_empty_oreg_never.
       firstorder.
    - pose proof mmatch_querypos_never.
      pose proof omatch_empty_oreg_never.
      firstorder.
    - pose proof mmatch_queryneg_never.
      pose proof omatch_empty_oreg_never.
      firstorder.
    - intros.
      setoid_rewrite mmatch_concat_iff.
      setoid_rewrite omatch_union_iff. 2: auto.
      setoid_rewrite omatch_concat_iff. 2: auto.
      split; intros.
      + rewrite IHmr2 in H0 by auto.
        setoid_rewrite <- IHmr1. 2: now apply ofirstn_outer_length_wf.
        auto.
      + rewrite IHmr2 by auto.
        setoid_rewrite <- IHmr1 in H0. 2: now apply ofirstn_outer_length_wf.
        auto. 
    - setoid_rewrite mmatch_union_iff.
      setoid_rewrite omatch_union_iff.
      firstorder.
    - intros.
      setoid_rewrite mmatch_star_iff. 2: auto.
      setoid_rewrite omatch_concat_iff. 2: auto.
      split; intros.
      + setoid_rewrite IHmr in H0. 2: now apply ofirstn_outer_length_wf.
        auto.
      + setoid_rewrite IHmr. 2: now apply ofirstn_outer_length_wf.
        auto.
Qed.

Lemma no_marked_never (mr : MRegex) :
    is_marked mr = false
    -> forall (os : ostring),
       outer_length_wf os ->
        ~ match_mregex mr os.
Proof.
  induction mr.
  - intros. now apply mmatch_eps_never.
  - intros. simpl in H. subst.
    now apply mmatch_unmarked_never.
  - intros.
    now apply mmatch_querypos_never.
  - intros.
    now apply mmatch_queryneg_never.
  - intros. simpl in H.
    apply Bool.orb_false_elim in H as [H1 H2].
    specialize (IHmr1 H1).
    specialize (IHmr2 H2).
    intro.
    apply mmatch_concat_iff in H. 2 : auto. 
    destruct H as [[n [X1 [X2 X3]]] | H].
    + apply IHmr1 in X2. contradiction. apply ofirstn_outer_length_wf. auto.
    + apply IHmr2 in H. contradiction. auto.
  - intros. simpl in H.
    apply Bool.orb_false_elim in H as [H1 H2].
    specialize (IHmr1 H1).
    specialize (IHmr2 H2).
    intro.
    apply mmatch_union_iff in H.
    destruct H as [H | H].
    + apply IHmr1 in H. contradiction. auto.
    + apply IHmr2 in H. contradiction. auto.
  - intros. simpl in H.
    specialize (IHmr H).
    intro.
    apply mmatch_star_iff in H1. 2 : auto.
    destruct H1 as [n [X1 [X2 X3]]].
    apply IHmr in X2. contradiction.
    apply ofirstn_outer_length_wf. auto.
Qed.

Lemma mmatch_no_empty_strings : forall (mr : MRegex) (os : ostring),
    match_mregex mr os ->
    olength os > 0.
Proof.
  induction mr; intros ? M.
  - specialize (mmatch_eps_never _ M). contradiction.
  - destruct b.
    + rewrite mmatch_marked_iff in M.
      destruct M as [a [H1 H2]].
      unfold olength. rewrite H1. simpl. lia.
    + specialize (mmatch_unmarked_never _ _ M). contradiction.
  - specialize (mmatch_querypos_never _ _ M). contradiction.
  - specialize (mmatch_queryneg_never _ _ M). contradiction.
  - inversion M; subst.
    + apply IHmr1 in H1.
      rewrite ofirstn_olength in H1. lia.
    + apply IHmr2 in H2; auto.
  - apply mmatch_union_iff in M.
    destruct M as [M | M].
    + apply IHmr1 in M; auto.
    + apply IHmr2 in M; auto.
  - inversion M; subst.  
    apply IHmr in H0; auto.
    rewrite ofirstn_olength in H0. lia.
Qed.


Lemma nullableWith_iff : forall (mr : MRegex) (v : valuation),
    nullableWith v mr = true <-> match_oregex (strip mr) ([], [v]).
Proof.
 induction mr; simpl; split.
 (* ε *)
 - intros. constructor. auto.
 - auto.
 (* CharClass *)
 - discriminate.
 - intros. inversion H; subst. unfold olength in H1. simpl in H1. discriminate. 
 (* QueryPos *) 
 - destruct (nth_error v n) eqn:En; [ destruct b | ].
   2, 3: discriminate.
   intros. apply omatch_query_pos with (v := v); auto.
 - intros. inversion H; subst.
   simpl in H2. inversion H2; subst.
   now rewrite H3.
 (* QueryNeg *) 
 - destruct (nth_error v n) eqn:En; [ destruct b | ].
   1, 3: discriminate.
   intros. apply omatch_query_neg with (v := v); auto.
 - intros. inversion H; subst.
   simpl in H2. inversion H2; subst.
   now rewrite H3.
 (* Concat *) 
 - rewrite Bool.andb_true_iff.
   intros [H1 H2].
   specialize (IHmr1 v). specialize (IHmr2 v).
   apply IHmr1 in H1. apply IHmr2 in H2.
   apply omatch_concat with (n := 0).
   + unfold ofirstn. simpl. auto.
   + unfold oskipn. simpl. auto.
 - rewrite Bool.andb_true_iff.
   intro M.
   apply omatch_concat_iff in M.
   2 : { unfold outer_length_wf. auto. } 
   destruct M as [n [M1 [M2 M3]]].
   specialize (IHmr1 v). specialize (IHmr2 v).
   replace (ofirstn n ([], [v])) with (@nil A, [v]) in M2.
     2 : { destruct n;  unfold ofirstn; auto. }
   replace (oskipn n ([], [v])) with (@nil A, [v]) in M3.
     2 : { destruct n; unfold oskipn; auto. }
   apply <- IHmr1 in M2. apply <- IHmr2 in M3.
   auto.
 (* Union *)
 - rewrite Bool.orb_true_iff.
   intros [H1 | H2].
   + apply omatch_union_l. apply IHmr1. auto.
   + apply omatch_union_r. apply IHmr2. auto.
 - rewrite Bool.orb_true_iff.
   intros M.
   inversion M; subst.
   + left. apply <- IHmr1. auto.
   + right. apply <- IHmr2. auto.
 (* Star *) 
 - intros.
   apply omatch_star_nonempty.
   + unfold outer_length_wf. auto.
   + left. auto.
 - auto.
Qed.



Lemma finalWith_fw : forall (mr : MRegex) (v1 : valuation),
    no_spurious_marks mr
    -> finalWith v1 mr = true
    -> exists a, forall v0, match_mregex mr ([a], [v0 ; v1]).
Proof. 
 induction mr; simpl; intros v1 N Hf.
 (* ε *)
 - discriminate. 
 (* CharClass *)
 - subst b. destruct N as [a N].
   exists a. intros.
   apply mmatch_charclass with (a := a) ; auto.
 (* QueryPos *) 
 - discriminate.
 (* QueryNeg *)
 - discriminate.
 (* Concat *) 
 - destruct N as [N1 N2].
  apply Bool.orb_true_iff in Hf as [Hf | Hf].
  + apply Bool.andb_true_iff in Hf as [Hf1 Hf2].
    specialize (IHmr1 v1 N1 Hf1).
    destruct IHmr1 as [a IHmr1].
    rewrite nullableWith_iff in Hf2.
    exists a. intro v0.
    apply mmatch_concat_l with (n := 1).
    * unfold ofirstn. simpl. auto.
    * unfold oskipn. simpl. auto.
  + specialize (IHmr2 v1 N2 Hf).
    destruct IHmr2 as [a IHmr2].
    exists a. intro v0.
    apply mmatch_concat_r.
    auto.
 (* Union *) 
 - destruct N as [N1 N2].
  apply Bool.orb_true_iff in Hf as [Hf | Hf].
  + specialize (IHmr1 v1 N1 Hf).
    destruct IHmr1 as [a IHmr1].
    exists a. intro v0.
    apply mmatch_union_l.
    auto.
  + specialize (IHmr2 v1 N2 Hf).
    destruct IHmr2 as [a IHmr2].
    exists a. intro v0.
    apply mmatch_union_r.
    auto.
 (* Star *)
 - specialize (IHmr v1 N Hf).
  destruct IHmr as [a IHmr].
  exists a. intro v0.
  apply mmatch_star with (n := 1).
  + unfold ofirstn. simpl. auto.
  + unfold oskipn. simpl. apply omatch_star_eps.
    reflexivity.
Qed.

Lemma finalWith_bw : forall (mr : MRegex) (v0 v1 : valuation) (a : A),
    match_mregex mr ([a], [v0 ; v1])
    -> finalWith v1 mr = true.
Proof.
  intros ? ? ? ? M.
  induction mr; simpl.
  (* ε *)
  - pose proof mmatch_eps_never _ M. contradiction.
  (* CharClass *)
  - destruct b.
    + inversion M; subst.
      simpl in H2. inversion H2; subst.
      auto.
    + pose proof mmatch_unmarked_never _ _ M. contradiction.
  (* QueryPos *)
  - pose proof mmatch_querypos_never _ _ M. contradiction.
  (* QueryNeg *)
  - pose proof mmatch_queryneg_never _ _ M. contradiction.
  (* Concat *)
  - apply mmatch_concat_iff in M. 2 : { unfold outer_length_wf. auto. }
    destruct M as [[n [M1 [M2 M3]]] | M].
    + unfold olength in M1. simpl in M1.
      assert (n = 0 \/ n = 1) as [Hn | Hn] by lia.
      * subst. 
        unfold ofirstn in M2. simpl in M2.
        unfold oskipn in M3. simpl in M3.
        pose proof mmatch_no_empty_strings mr1 ([], [v0]).
        specialize (H M2).
        unfold olength in H. simpl in H. lia.
      * subst. 
        unfold ofirstn in M2. simpl in M2.
        unfold oskipn in M3. simpl in M3.
        specialize (IHmr1 M2).
        rewrite <- nullableWith_iff in M3.
        rewrite M3. rewrite IHmr1.
        auto.
    + apply IHmr2 in M.
      rewrite Bool.orb_true_iff.
      auto.
  (* Union *)
  - apply mmatch_union_iff in M.
    destruct M as [M | M].
    + apply IHmr1 in M.
      rewrite Bool.orb_true_iff.
      auto.
    + apply IHmr2 in M.
      rewrite Bool.orb_true_iff.
      auto.
  (* Star *)
  - apply mmatch_star_iff in M. 2 : { unfold outer_length_wf. auto. }
    destruct M as [n [M1 [M2 M3]]].
    unfold olength in M1. simpl in M1.
    assert (n = 0 \/ n = 1) as [Hn | Hn] by lia.
    + subst. 
      unfold ofirstn in M2. simpl in M2.
      unfold oskipn in M3. simpl in M3.
      pose proof mmatch_no_empty_strings mr ([], [v0]).
      specialize (H M2).
      unfold olength in H. simpl in H. lia.
    + subst.
      unfold ofirstn in M2. simpl in M2.
      unfold oskipn in M3. simpl in M3.
      apply IHmr in M2.
      rewrite M2.
      auto.
Qed.

Lemma finalWith_bw1 : forall (mr : MRegex) (v1 : valuation) (a : A),
    (forall v0, match_mregex mr ([a], [v0 ; v1]))
    -> finalWith v1 mr = true.
Proof.
  intros ? ? ? M.
  pose proof finalWith_bw as H.
  specialize (H mr v1 v1 a (M _)).
  auto.
Qed.


Lemma finalWith_iff : forall (mr : MRegex) (v1: valuation),
    no_spurious_marks mr
    -> finalWith v1 mr = true
    <-> exists a, forall v0, match_mregex mr ([a], [v0 ; v1]).
Proof.
  pose proof finalWith_fw as FW.
  pose proof finalWith_bw1 as BW.
  intros ? ? N.
  split; intros.
  - apply FW in H; auto.
  - destruct H as [a H].
    exact (BW mr v1 a H).
Qed.

Lemma read_no_spurious : forall (mr : MRegex) (a : A),
    no_spurious_marks (read a mr).
Proof.
  induction mr; simpl; intros ?; auto.
  (* CharClass *)
  destruct b;
  destruct (b0 a) eqn:Eb; try reflexivity.
  exists a; auto. 
Qed.

Lemma strip_read : forall (mr : MRegex) (a : A),
    strip (read a mr) = strip mr.
Proof.
  induction mr; simpl; intros; congruence.
Qed.

Lemma read_fw (mr : MRegex) (a : A) (os : ostring) :
  outer_length_wf os
  -> match_mregex mr os
  -> hd_error (fst os) = Some a
  -> match_mregex (read a mr) os.
Proof.
  revert a os.
  induction mr; simpl; intros a os Hwf M H.
  (* ε *)
  - pose proof mmatch_eps_never _ M. contradiction.
  (* CharClass *)
  - destruct b eqn:Eb.
    2 : { pose proof mmatch_unmarked_never _ _ M. contradiction. }
    rewrite mmatch_marked_iff in M.
    destruct M as [a0 [H1 H2]].
    rewrite H1 in H. simpl in H.
    inversion H; subst a0.
    rewrite H2. simpl.
    apply mmatch_charclass with (a := a); auto.
    + unfold olength. rewrite H1. auto.
    + rewrite H1. auto. 
  (* QueryPos *)
  - pose proof mmatch_querypos_never _ _ M. contradiction.
  (* QueryNeg *)
  - pose proof mmatch_queryneg_never _ _ M. contradiction.
  (* Concat *)
  - apply mmatch_concat_iff in M. 
    2 : { unfold outer_length_wf. auto. }
    destruct M as [[n [M1 [M2 M3]]] | M].
    + apply IHmr1 with (a := a) in M2.
      * apply mmatch_concat_l with (n := n); auto.
      rewrite strip_read. auto.
      * apply ofirstn_outer_length_wf. auto.
      * destruct n.
      { pose proof (mmatch_no_empty_strings mr1 (ofirstn 0 os)). 
      specialize (H0 M2).
      rewrite ofirstn_olength in H0. lia. }
      { destruct os as (w, o).
        simpl.
        destruct w; [ inversion H | ].
        simpl in H. inversion H; subst a0.
        auto.
      }
    + apply IHmr2 with (a := a) in M.
      * apply mmatch_concat_r; auto.
      * auto.
      * auto.    
  (* Union *) 
  - apply mmatch_union_iff in M.
    destruct M as [M | M].
    + apply IHmr1 with (a := a) in M.
      * apply mmatch_union_l; auto.
      * auto.
      * auto.
    + apply IHmr2 with (a := a) in M.
      * apply mmatch_union_r; auto.
      * auto.
      * auto.
  (* Star *)
  - apply mmatch_star_iff in M.
    2 : { unfold outer_length_wf. auto. }
    destruct M as [n [M1 [M2 M3]]].
    destruct n.
    { pose proof (mmatch_no_empty_strings mr (ofirstn 0 os)). 
      specialize (H0 M2).
      rewrite ofirstn_olength in H0. lia. }
    apply IHmr with (a := a) in M2.
    2 : { apply ofirstn_outer_length_wf. auto. }
    2 : { destruct os as (w, o).
          simpl.
          destruct w; [ inversion H | ].
          simpl in H. inversion H; subst a0.
          auto.
    }
    apply mmatch_star with (n := S n); auto.
    rewrite strip_read. auto.
Qed.

Lemma read_subset (mr : MRegex) (a : A) (os : ostring) :
  outer_length_wf os
  -> match_mregex (read a mr) os
  -> match_mregex mr os.
Proof.
  revert a os.
  induction mr; simpl; intros a os Hwf M.
  (* ε *)
  - pose proof mmatch_eps_never _ M. contradiction.
  (* CharClass *)
  - destruct b eqn:Eb.
    2 : { pose proof mmatch_unmarked_never _ _ M. contradiction. }
    simpl in M.
    destruct (b0 a) eqn:Eb0.
    2 : { pose proof mmatch_unmarked_never _ _ M. contradiction. }
    auto.
  (* QueryPos *)
  - pose proof mmatch_querypos_never _ _ M. contradiction.
  (* QueryNeg *)
  - pose proof mmatch_queryneg_never _ _ M. contradiction.
  (* Concat *)
  - apply mmatch_concat_iff in M. 
    2 : { unfold outer_length_wf. auto. }
    destruct M as [[n [M1 [M2 M3]]] | M].
    + apply IHmr1 with (a := a) in M2.
      2 : { apply ofirstn_outer_length_wf. auto. }
      rewrite strip_read in M3.
      apply mmatch_concat_l with (n := n); auto.
    + apply IHmr2 with (a := a) in M.
      2 : { unfold outer_length_wf. auto. }
      apply mmatch_concat_r; auto.       
  (* Union *) 
  - rewrite mmatch_union_iff.
    rewrite mmatch_union_iff in M.
    firstorder.
  (* Star *)
  - apply mmatch_star_iff in M.
    2 : { unfold outer_length_wf. auto. }
    destruct M as [n [M1 [M2 M3]]].
    apply IHmr with (a := a) in M2.
    2 : { apply ofirstn_outer_length_wf. auto. }
    rewrite strip_read in M3.
    apply mmatch_star with (n := n); auto.
Qed.

Lemma read_bw (mr : MRegex) (a : A) (os : ostring) :
  outer_length_wf os
  -> match_mregex (read a mr) os
  -> match_mregex mr (a :: tl (fst os), snd os).
Proof.
  revert a os.
  induction mr; simpl; intros a os Hwf M.
  (* ε *)
  - pose proof mmatch_eps_never _ M. contradiction.
  (* CharClass *)
  - destruct b eqn:Eb.
    2 : { pose proof mmatch_unmarked_never _ _ M. contradiction. }
    simpl in M.
    destruct (b0 a) eqn:Eb0.
    2 : { pose proof mmatch_unmarked_never _ _ M. contradiction. }
    inversion M; subst.
    destruct os as (w, o).
    simpl in Hwf. destruct w.
    { simpl in H1. discriminate. }
    simpl. apply mmatch_charclass with (a := a); auto.
  (* QueryPos *)
  - pose proof mmatch_querypos_never _ _ M. contradiction.
  (* QueryNeg *)
  - pose proof mmatch_queryneg_never _ _ M. contradiction.
  (* Concat *)
  - apply mmatch_concat_iff in M. 
    2 : { unfold outer_length_wf. auto. }
    destruct M as [[n [M1 [M2 M3]]] | M].
    + pose proof (mmatch_no_empty_strings _ _ M2).
      rewrite ofirstn_olength in H. 
      assert (n > 0) as Hn by lia.
      destruct n as [ | n]. 
      { lia. }
      assert (olength os > 0) as Hn' by lia.
      destruct os as (w, o).
      destruct w; [ inversion Hn' | ].
      simpl. 
      specialize (IHmr1 a (ofirstn (S n) (a0 :: w, o)) 
        ltac:(auto using ofirstn_outer_length_wf) M2).
      rewrite strip_read in M3.
      apply mmatch_concat_l with (n := S n).
      * unfold ofirstn in *. 
        remember (S n) as n'.
        remember (S n') as n''.
        simpl in *. 
        subst n'. simpl firstn in IHmr1. simpl tl in IHmr1. auto.
      * unfold oskipn in M3 |- *.
        remember (S n) as n'.
        simpl in M3 |- *.
        subst n'. auto.
    + apply IHmr2 with (a := a) in M.
      2 : { unfold outer_length_wf. auto. }
      apply mmatch_concat_r; auto.       
  (* Union *)
  - rewrite mmatch_union_iff.
    rewrite mmatch_union_iff in M.
    firstorder.
  (* Star *)
  - apply mmatch_star_iff in M.
    2 : { unfold outer_length_wf. auto. }
    destruct M as [n [M1 [M2 M3]]].
    pose proof (mmatch_no_empty_strings _ _ M2).
    rewrite ofirstn_olength in H. 
    assert (n > 0) as Hn by lia.
    destruct n as [ | n]. 
    { lia. }
    assert (olength os > 0) as Hn' by lia.
    destruct os as (w, o).
    destruct w; [ inversion Hn' | ].
    simpl.
    specialize (IHmr a (ofirstn (S n) (a0 :: w, o)) 
      ltac:(auto using ofirstn_outer_length_wf) M2).
    rewrite strip_read in M3.
    apply mmatch_star with (n := S n).
    + unfold ofirstn in *. 
      remember (S n) as n'.
      remember (S n') as n''.
      simpl in *. 
      subst n'. simpl firstn in IHmr. simpl tl in IHmr. auto.
    + unfold oskipn in M3 |- *.
      remember (S n) as n'.
      simpl in M3 |- *.
      subst n'. auto.
Qed.

Lemma initMarkWith_strip : forall (mr : MRegex) (v : valuation),
    strip (initMarkWith v mr) = strip mr.
Proof.
  induction mr; simpl; intros; try congruence.
  (* Concat *)
  - destruct (nullableWith v mr1) eqn:En; congruence.
Qed.

Lemma initMarkWith_nullWith (mr : MRegex) (v : valuation) :
  nullableWith v (initMarkWith v mr) = nullableWith v mr.
Proof.
  intros.
  pose proof (nullableWith_iff mr v).
  pose proof (nullableWith_iff (initMarkWith v mr) v).
  rewrite initMarkWith_strip in H0.
  destruct (nullableWith v mr) eqn:En;
  destruct (nullableWith v (initMarkWith v mr)) eqn:En'; 
  firstorder.
Qed.

Lemma initMarkWith_idempotent (mr : MRegex) (v : valuation) :
    initMarkWith v (initMarkWith v mr) = initMarkWith v mr.
Proof.
  induction mr; simpl; intros; try congruence.
  (* Concat *)
  rewrite initMarkWith_nullWith.
  destruct (nullableWith v mr1) eqn:En; congruence.
Qed.

Lemma initMarkWith_superset (mr : MRegex) (v : valuation):
  forall (os : ostring),
    outer_length_wf os
    -> match_mregex mr os
    -> match_mregex (initMarkWith v mr) os.
Proof.
  induction mr; simpl; intros os Hwf M.
  (* ε *)
  - pose proof mmatch_eps_never _ M. contradiction.
  - destruct b eqn:Eb.
  (* CharClass *)
    2 : { pose proof mmatch_unmarked_never _ _ M. contradiction. }
    auto.
  (* QueryPos *)
  - pose proof mmatch_querypos_never _ _ M. contradiction.
  (* QueryNeg *)
  - pose proof mmatch_queryneg_never _ _ M. contradiction.
  (* Concat *)
  - apply mmatch_concat_iff in M.
    2 : { unfold outer_length_wf. auto. }
    destruct M as [[n [M1 [M2 M3]]] | M].
    + apply IHmr1 in M2.
      2 : { apply ofirstn_outer_length_wf. auto. }
      apply mmatch_concat_l with (n := n); auto.
      destruct (nullableWith v mr1).
      * now rewrite initMarkWith_strip.
      * auto. 
    + destruct (nullableWith v mr1);
        apply mmatch_concat_r; auto. 
  (* Union *)
  - apply mmatch_union_iff in M.
    rewrite mmatch_union_iff.
    firstorder.
  (* Star *)
  - apply mmatch_star_iff in M.
    2 : { unfold outer_length_wf. auto. }
    destruct M as [n [M1 [M2 M3]]].
    apply IHmr with (os := ofirstn n os) in M2.
    2 : { apply ofirstn_outer_length_wf. auto. }
    apply mmatch_star with (n := n); auto.
    now rewrite initMarkWith_strip.
Qed.

Lemma stripLang_in_initMarkWith (mr : MRegex) (v0 : valuation) :
  forall (os : ostring),
    outer_length_wf os
    -> olength os > 0
    -> hd_error (snd os) = Some v0
    -> match_oregex (strip mr) os
    -> match_mregex (initMarkWith v0 mr) os.
Proof.
  induction mr; simpl; intros os Hwf H1 H2 M.
  (* ε *){
  inversion M.
  lia.
  }
  (* CharClass *){
  now rewrite mmatch_markedLang_iff by auto.
  }
  (* QueryPos *){
  inversion M. lia.
  }
  (* QueryNeg *){
  inversion M. lia.
  }
  (* Concat *){
  rewrite omatch_concat_iff in M.
  2 : { unfold outer_length_wf. auto. }
  destruct M as [n [M1 [M2 M3]]].
  assert (n = 0 \/ n > 0) as [Hn | Hn] by lia.
  - subst n.
  apply mmatch_concat_r.
  destruct os as (w, o).
  unfold oskipn in M3. simpl in M3.
  destruct (nullableWith v0 mr1) eqn:En.
    + apply IHmr2; auto.
    + pose proof (nullableWith_iff mr1 v0) as N.
      enough (match_oregex (strip mr1) ([], [v0])).
      { rewrite <- N in H. congruence. }
      unfold ofirstn in M2. simpl in M2.
      destruct o.
      { unfold olength in H1. unfold outer_length_wf in Hwf. simpl in *. lia. }
      simpl in H2. inversion H2; subst v. auto.
  - apply mmatch_concat_l with (n := n).
    + apply IHmr1; auto.
      * apply ofirstn_outer_length_wf. auto.
      * rewrite ofirstn_olength. lia.
      * unfold ofirstn. destruct os as (w, o).
        unfold olength in H1. unfold outer_length_wf in Hwf. simpl in *.
        destruct o; simpl in *. { lia. }
        auto. 
    + destruct (nullableWith v0 mr1) eqn:En.
      * rewrite initMarkWith_strip.
        auto.
      * auto.
  }
  (* Union *){
  rewrite mmatch_union_iff.
  rewrite omatch_union_iff in M.
  firstorder.
  }
  (* Star *){
  rewrite omatch_star_nonempty in M.
  2 : { unfold outer_length_wf. auto. }
  destruct M as [M | M]; [lia | ].
  destruct M as [n [M1 [M2 [M3 M4]]]].
  apply mmatch_star with (n := n).
  - apply IHmr.
    + apply ofirstn_outer_length_wf. auto.
    + rewrite ofirstn_olength. lia.
    + unfold ofirstn. destruct os as (w, o).
      unfold olength in H1. unfold outer_length_wf in Hwf. simpl in *.
      destruct o; simpl in *. { lia. }
      auto.
    + auto. 
  - rewrite initMarkWith_strip.
    auto. 
  }
Qed.

Lemma initMarkWith_bw (mr : MRegex) (v0 : valuation) :
  forall (os : ostring),
    outer_length_wf os
    -> match_mregex (initMarkWith v0 mr) os
    -> olength os > 0
    /\ (match_oregex (strip mr) (fst os, (v0 :: tl (snd os)))
    \/ match_mregex mr os)
    .
Proof.
  induction mr; simpl; intros os Hwf M.
  (* ε *)
  { pose proof mmatch_eps_never _ M. contradiction. }
  (* CharClass *) {
  inversion M; subst.
  split; [lia | ].
  left. apply omatch_charclass with (a := a); auto.
  }
  (* QueryPos *) {
  pose proof mmatch_querypos_never _ _ M. contradiction.
  }
  (* QueryNeg *) {
  pose proof mmatch_queryneg_never _ _ M. contradiction.
  }
  (* Concat *) {
  apply mmatch_concat_iff in M.
  2 : { unfold outer_length_wf. auto. }
  destruct M as [[n [M1 [M2 M3]]] | M].
  - apply IHmr1 in M2.
    2 : { apply ofirstn_outer_length_wf. auto. }
    destruct M2 as [H1 H2].
    assert (olength os > 0) as Los.
    { rewrite ofirstn_olength in H1. lia. }
    split; [lia | ].
    destruct H2 as [H2 | H2].
    + left.
      destruct os as (w, o).
      apply omatch_concat with (n := n).
      * unfold ofirstn in *. simpl fst in *.
        simpl snd in *.
        destruct o. { unfold outer_length_wf in Hwf. simpl in *. lia. }
        simpl in *. auto.
      * unfold oskipn in *. simpl in *.
        enough (skipn (Nat.min n (length w)) o = skipn (Nat.min n (length w)) (v0 :: tl o)).
        { rewrite <- H. auto. 
          destruct (nullableWith v0 mr1) eqn:En.
          - rewrite initMarkWith_strip in M3. auto.
          - auto.
        }
        unfold outer_length_wf in Hwf. simpl in Hwf.
        unfold olength in Los, H1. simpl in Los, H1.
        rewrite firstn_length in H1.
        destruct w. { simpl in *. lia. }
        destruct o. { simpl in *. lia. }
        simpl in H1.
        destruct n. { simpl in *. lia. }
        auto.
    + right.
      apply mmatch_concat_l with (n := n); auto.
      destruct (nullableWith v0 mr1) eqn:En.
      * rewrite initMarkWith_strip in M3. auto.
      * auto. 
  - destruct (nullableWith v0 mr1) eqn:En.
    + rewrite nullableWith_iff in En.
      specialize (IHmr2 os Hwf M).
      destruct IHmr2 as [Hlen H].
      split; [assumption | ].
      destruct H as [H | H].
      * left.
        apply omatch_concat with (n := 0).
        { unfold ofirstn. simpl. auto. }
        { unfold oskipn. simpl. auto. }
      * right.
        apply mmatch_concat_r; auto. 
    + split.
      { eapply mmatch_no_empty_strings; eauto. }
      { right. apply mmatch_concat_r. assumption. }
  }
  (* Union *) {  
  rewrite mmatch_union_iff in M.
  destruct M as [M | M].
  - apply IHmr1 in M.
    2 : { assumption. }
    destruct M as [H1 H2].
    split; [lia | ].
    destruct H2 as [H2 | H2].
    + left.
      apply omatch_union_l; auto.
    + right.
      apply mmatch_union_l; auto. 
  - apply IHmr2 in M.
    2 : { assumption. }
    destruct M as [H1 H2].
    split; [lia | ].
    destruct H2 as [H2 | H2].
    + left.
      apply omatch_union_r; auto.
    + right.
      apply mmatch_union_r; auto.
  }
  (* Star *) {
  rewrite mmatch_star_iff in M.
  2 : { unfold outer_length_wf. auto. }
  destruct M as [n [M1 [M2 M3]]].
  assert (outer_length_wf (ofirstn n os)) as Hwf'.
  { apply ofirstn_outer_length_wf. auto. }
  specialize (IHmr _ Hwf' M2).
  destruct IHmr as [Hlen H].
  rewrite ofirstn_olength in Hlen.
  split; [lia | ].
  destruct H as [H | H].
  - left.
    apply omatch_star with (n := n).
    + destruct os as (w, o).
      unfold ofirstn in *. simpl fst in *.
      simpl snd in *.
      destruct o. { unfold outer_length_wf in Hwf. simpl in *. lia. }
      simpl in *. auto.
    + rewrite initMarkWith_strip in M3.
      destruct os as (w, o).
      unfold oskipn in *. simpl in *.
      enough (skipn (Nat.min n (length w)) o = skipn (Nat.min n (length w)) (v0 :: tl o)).
      { rewrite <- H0. auto. }
      unfold outer_length_wf in Hwf. simpl in Hwf.
      unfold olength in Hlen. simpl in Hlen.
      destruct w. { simpl in *. lia. }
      destruct o. { simpl in *. lia. }
      simpl in Hlen.
      destruct n. { simpl in *. lia. }
      auto.
  - right.
    apply mmatch_star with (n := n); auto.
    rewrite initMarkWith_strip in M3.
    auto. 
  }
Qed.

Lemma shiftWith_strip : forall (mr : MRegex) (v : valuation),
    strip (shiftWith v mr) = strip mr.
Proof.
  induction mr; simpl; intros; try congruence.
  (* Concat *)
  - destruct (finalWith v mr1) eqn:Ef.
    + rewrite initMarkWith_strip. congruence.
    + congruence.
  (* Star *)
  - destruct (finalWith v mr) eqn:Ef.
    + rewrite initMarkWith_strip. congruence.
    + congruence.
Qed.

Lemma shiftWith_fw (mr : MRegex) (v : valuation) (os : @ostring A) :
  outer_length_wf os
  -> olength os > 1
  -> hd_error (tl (snd os)) = Some v
  -> match_mregex mr os
  -> match_mregex (shiftWith v mr) (oskipn 1 os).
Proof.
  revert v os.
  induction mr; simpl; intros v os Hwf Hlen H M.
  (* ε *)
  { pose proof mmatch_eps_never _ M. contradiction. }
  (* CharClass *)
  { destruct b eqn:Eb.
    + rewrite mmatch_marked_iff in M.
      destruct M as [a [M1 M2]].
      unfold olength in Hlen. rewrite M1 in Hlen.
      simpl in Hlen. lia.
    + pose proof mmatch_unmarked_never _ _ M. contradiction.
  }
  (* QueryPos *)
  { pose proof mmatch_querypos_never _ _ M. contradiction. }
  (* QueryNeg *)
  { pose proof mmatch_queryneg_never _ _ M. contradiction. }
  (* Concat *) {
  apply mmatch_concat_iff in M. 2 : { apply Hwf. }
  destruct M as [[n [M1 [M2 M3]]] | M].
  (* when we have os \in stripLang mr2 *)
  2 : {
    apply IHmr2 with (v := v) in M; auto.
    apply mmatch_concat_r.
    destruct (finalWith v mr1) eqn:Ef.
    + apply initMarkWith_superset; auto.
      apply oskipn_outer_length_wf; auto.
    + auto.
  }
  (* n can't be 0 *)
  destruct n as [ | n'] . {
    destruct os as (w, o).
    pose proof (mmatch_no_empty_strings mr1 (ofirstn 0 (w, o))).
    specialize (H0 M2).
    rewrite ofirstn_olength in H0. simpl in H0. lia.
  }
  (* when n = 1, we know that the finalWith is true *)
  destruct n' as [ | n'']. {
    destruct os as (w, o).
    unfold outer_length_wf in Hwf. simpl in Hwf.
    unfold olength in Hlen. simpl in Hlen.
    destruct w as [ | w0 w']. { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. { simpl in Hwf. lia. }
    destruct o' as [ | o1 o']. { simpl in Hwf. lia. }
    unfold ofirstn in M2. simpl in M2.
    unfold oskipn in M3. simpl in M3.
    simpl in H. inversion H; subst v.
    pose proof (finalWith_bw _ _ _ _ M2) as F.
    rewrite F.
    apply mmatch_concat_r.
    unfold oskipn. simpl.
    apply stripLang_in_initMarkWith.
    - unfold outer_length_wf. simpl in *. lia.
    - unfold olength. simpl in *. lia.
    - auto.
    - rewrite shiftWith_strip. auto.
  }
  (* when n > 1, we use IHmr1 to make the left side smaller *)
  destruct os as (w, o).
  unfold outer_length_wf in Hwf. simpl in Hwf.
  unfold olength in Hlen. simpl in Hlen.
  destruct w as [ | w0 w']. { simpl in Hlen. lia. }
  destruct o as [ | o0 o']. { simpl in Hwf. lia. }
  destruct o' as [ | o1 o']. { simpl in Hwf. lia. }
  unfold ofirstn in M2. simpl fst in M2. simpl snd in M2.
  remember (S n'') as n1. simpl in M2.
  unfold oskipn in M3. simpl in M3.
  assert (n1 <= length w') as Hn1. {
    unfold olength in *. simpl in *. lia.
  }
  replace (min n1 (length w')) with n1 in M3 by lia.
  unfold oskipn. simpl.
  apply IHmr1 with (v := v) in M2. 
  unfold oskipn in M2. simpl in M2.
  - apply mmatch_concat_l with (n := n1); auto.
    destruct (finalWith v mr1) eqn:Ef.
    + rewrite initMarkWith_strip.
      rewrite shiftWith_strip.
      unfold oskipn. simpl.
      replace (min n1 (length w')) with n1 by lia.
      auto.
    + rewrite shiftWith_strip.
    unfold oskipn. simpl.
    replace (min n1 (length w')) with n1 by lia.
    auto.
  - unfold outer_length_wf. unfold olength in *. simpl in *.
    repeat rewrite firstn_length. lia.
  - unfold olength. simpl. rewrite firstn_length. lia.
  - simpl in H. simpl. auto. 
  }
  (* Union *){
    rewrite mmatch_union_iff.
    rewrite mmatch_union_iff in M.
    firstorder.
  }
  (* Star *){
    apply mmatch_star_iff in M. 2 : { apply Hwf. }
    destruct M as [n [M1 [M2 M3]]].
    destruct n as [ | n']. {
      (* n can't be 0 *)
      destruct os as (w, o).
      pose proof (mmatch_no_empty_strings mr (ofirstn 0 (w, o))).
      specialize (H0 M2).
      rewrite ofirstn_olength in H0. simpl in H0. lia.
    }
    destruct n' as [ | n'']. {
      (* when n = 1, we know that the finalWith is true *)
      destruct os as (w, o).
      unfold outer_length_wf in Hwf. simpl in Hwf.
      unfold olength in Hlen. simpl in Hlen.
      destruct w as [ | w0 w']. { simpl in Hlen. lia. }
      destruct o as [ | o0 o']. { simpl in Hwf. lia. }
      destruct o' as [ | o1 o']. { simpl in Hwf. lia. }
      unfold ofirstn in M2. simpl in M2.
      unfold oskipn in M3. simpl in M3.
      simpl in H. inversion H; subst v.
      pose proof (finalWith_bw _ _ _ _ M2) as F.
      rewrite F.
      unfold oskipn. simpl.
      replace (MStar (initMarkWith o1 (shiftWith o1 mr)))
      with (initMarkWith o1 (MStar (shiftWith o1 mr))) by auto.
      apply stripLang_in_initMarkWith.
      + unfold outer_length_wf. simpl in Hwf. simpl. lia.
      + unfold olength. simpl fst.
        simpl in Hlen. lia.
      + auto.
      + simpl. rewrite shiftWith_strip. auto.
    }
    (* when n > 1, we use IHmr to make the left side smaller *)
    destruct os as (w, o).
    unfold outer_length_wf in Hwf. simpl in Hwf.
    unfold olength in Hlen. simpl in Hlen.
    destruct w as [ | w0 w']. { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. { simpl in Hwf. lia. }
    destruct o' as [ | o1 o']. { simpl in Hwf. lia. }
    unfold ofirstn in M2. simpl fst in M2. simpl snd in M2.
    remember (S n'') as n1. simpl in M2.
    unfold oskipn in M3. simpl in M3.
    assert (n1 <= length w') as Hn1. {
      unfold olength in *. simpl in *. lia.
    }
    replace (min n1 (length w')) with n1 in M3 by lia.
    unfold oskipn. simpl.
    apply IHmr with (v := o1) in M2.
    unfold oskipn in M2. simpl in M2.
    simpl in H. inversion H; subst v.
    destruct (finalWith o1 mr) eqn:Ef.
    - apply mmatch_star with (n := n1); auto.
      + apply initMarkWith_superset; auto.
        apply ofirstn_outer_length_wf.
        unfold outer_length_wf. simpl in Hwf. simpl. lia.
      + rewrite initMarkWith_strip.
        rewrite shiftWith_strip.
        unfold oskipn. simpl.
        replace (min n1 (length w')) with n1 by lia.
        auto. 
    - apply mmatch_star with (n := n1); auto.
      rewrite shiftWith_strip.
      unfold oskipn. simpl.
      replace (min n1 (length w')) with n1 by lia.
      auto.
    - unfold outer_length_wf. unfold olength in *. simpl in *.
      repeat rewrite firstn_length. lia.
    - unfold olength. simpl. rewrite firstn_length. lia.
    - auto.  
  }
Qed.
  
Lemma shiftWith_bw (mr : MRegex) (v1 : valuation) (os : @ostring A) :
  no_spurious_marks mr
  -> outer_length_wf os
  -> match_mregex (shiftWith v1 mr) os
  -> exists a, forall v0,
      match_mregex mr (a :: fst os, v0 :: v1 :: tl (snd os)).
Proof.
  revert v1 os.
  induction mr; intros v1 os Hspur Hwf M.
  (* ε *)
  { pose proof mmatch_eps_never _ M. contradiction. }
  (* CharClass *)
  { destruct b eqn:Eb; simpl in M;
      pose proof mmatch_unmarked_never _ _ M; contradiction.
  }
  (* QueryPos *)
  { pose proof mmatch_querypos_never _ _ M. contradiction. }
  (* QueryNeg *)
  { pose proof mmatch_queryneg_never _ _ M. contradiction. }
  (* Concat *) {
    simpl in M.
    rewrite mmatch_concat_iff in M. 2 : { apply Hwf. }
    destruct M as [[n [M1 [M2 M3]]] | M].
    
    (* here, the first case is easier.
        we have os \in (bulletLang _) · (stripLang _)
       In this case, we will use IHmr1 to expand the first part
       then, we can use match_concat_l to 
        glue back the expanded part with the second part
        that comes from the (stripLang _)
    *){
    (* lets notice that n can't be 0 *)
    destruct n as [ | n']. {
      destruct os as (w, o).
      pose proof (mmatch_no_empty_strings (shiftWith v1 mr1) (ofirstn 0 (w, o))).
      specialize (H M2).
      rewrite ofirstn_olength in H. simpl in H. lia.
    }
    apply IHmr1 in M2.
    2 : simpl in Hspur; tauto.
    2 : now apply ofirstn_outer_length_wf.
    replace (strip
      (if finalWith v1 mr1
      then initMarkWith v1 (shiftWith v1 mr2)
      else shiftWith v1 mr2)) with (strip mr2) in M3.
    2 : {
      destruct (finalWith v1 mr1) eqn:Ef.
      - rewrite initMarkWith_strip; rewrite shiftWith_strip; auto.
      - rewrite shiftWith_strip; auto.
    }
    destruct M2 as [a M2].
    exists a. intros v0. specialize (M2 v0).
    destruct os as (w, o). simpl.
    unfold ofirstn, oskipn in *. 
    remember (S n') as n.
    simpl fst in *. simpl snd in *.
    destruct o as [ | o0 o']. { 
      unfold outer_length_wf in Hwf. simpl in Hwf. lia.
    }
    destruct w as [ | w0 w']. { 
      unfold olength in M1. simpl in M1. lia.
    }
    destruct o' as [ | o1 o'']. { 
      unfold outer_length_wf in Hwf. simpl in Hwf. lia.
    }
    simpl in M2. simpl in M3.
    rewrite Heqn in M2. simpl in M2.
    rewrite Heqn in M3. simpl in M3.
    assert (n' <= length w') as Hn. {
      unfold olength in M1. simpl in M1. lia.
    }
    replace (min n' (length w')) with n' in M3 by lia.
    apply mmatch_concat_l with (n := S (S n')).
    - unfold ofirstn. subst n. simpl. auto.
    - unfold oskipn. simpl.
      replace (min n' (length w')) with n' by lia.
      auto. 
    }
    (* In the second case, we either have
            os \in bulletLang (shiftWith v1 mr2)
        or, os \in stripLang mr2
        In the first subcase, we use IHmr2 to expand os
          and then use match_concat_r to assert that
          the expanded part is in bulletLang (mr1 · mr2)
        If we are in the second subcase, we must have
          finalWith v1 mr1 = true
          This can means that there is a word of the form
          ([a], [v0, v1]) · os \in bulletLang (mr1 · mr2)
    *){
    cut (
        match_mregex (shiftWith v1 mr2) os
     \/ (finalWith v1 mr1 = true /\ match_oregex (strip mr2) (fst os, v1 :: tl (snd os))) 
    ).
    2 : {
      destruct (finalWith v1 mr1) eqn:Ef.
      - apply initMarkWith_bw in M. 2 : { apply Hwf. }
        destruct M as [_ [M | M]].
        + rewrite shiftWith_strip in M. auto.
        + auto. 
      - auto.
    } 
    intros [Mm | [F Mm]]. {
      (* this is when os \in bulletLang (shiftWith v1 mr2) *)
      apply IHmr2 in Mm.
      2 : simpl in Hspur; tauto.
      2 : auto.
      destruct Mm as [a Mm].
      exists a. intros v0. specialize (Mm v0).
      apply mmatch_concat_r; auto.
    } {
    (* this is when os \in stripLang mr2 *)
    apply finalWith_fw in F.
    2 : simpl in Hspur; tauto.
    destruct F as [a M1].
    exists a. intros v0. specialize (M1 v0).
    apply mmatch_concat_l with (n := 1).
    - unfold ofirstn. auto.
    - unfold oskipn. auto.
    }
    }
  }
  (* Union *) {
    simpl in M. rewrite mmatch_union_iff in M.
    destruct M as [M | M].
    - apply IHmr1 in M.
      2 : simpl in Hspur; tauto.
      2 : auto.
      destruct M as [a M].
      exists a. intros v0. specialize (M v0).
      apply mmatch_union_l; auto.
    - apply IHmr2 in M.
      2 : simpl in Hspur; tauto.
      2 : auto.
      destruct M as [a M].
      exists a. intros v0. specialize (M v0).
      apply mmatch_union_r; auto.
  }
  (* Star *) {
    simpl in M. 
    rewrite mmatch_star_iff in M. 2 : auto.
    destruct M as [n [M1 [M2 M3]]].
    (* lets notice that n can't be 0 *)
    destruct n as [ | n']. {
      destruct os as (w, o).
      pose proof (mmatch_no_empty_strings _ _ M2).
      rewrite ofirstn_olength in H. lia.
    }
    (* lets simply M3 into just (strip mr) *)
    replace (strip (if finalWith v1 mr
     then initMarkWith v1 (shiftWith v1 mr)
     else shiftWith v1 mr)) with (strip mr) in M3.
    2 : {
      destruct (finalWith v1 mr) eqn:Ef.
      - rewrite initMarkWith_strip; rewrite shiftWith_strip; auto.
      - rewrite shiftWith_strip; auto.
    }
    (* 
      Here, os can be split into two parts.
        Say os = os1 · os2
        We have that
          os1 \in bulletLang ...
          os2 \in stripLang mr
      If we examine os1, we can see two possibilies
        Case I: os1 \in bulletLang (shiftWith v1 mr)
          In this case, we use IHmr to expand os1
          and then glue back the expanded part with os2
        Case II: os1 \in stripLang mr
          In this case, we must have finalWith v1 mr = true
          This means that 
            ([a], [v0, v1]) \in bulletLang mr
          and os1 \in stripLang mr
          Thus, ([a], [v0, v1]) · os1 \in bulletLang (Star mr)
          So, we can glue back ([a], [v0, v1]) · os1 with os2
    *)
    remember (ofirstn (S n') os) as os1.
    remember (oskipn (S n') os) as os2.
    cut (
        match_mregex (shiftWith v1 mr) os1
     \/ (finalWith v1 mr = true /\ match_oregex (strip mr) (fst os1, v1 :: tl (snd os1))) 
    ).
    2 : {
      destruct (finalWith v1 mr) eqn:Ef.
      - apply initMarkWith_bw in M2. 2 : {
        subst os1. apply ofirstn_outer_length_wf. auto.
      }
        destruct M2 as [_ [M | M]].
        + rewrite shiftWith_strip in M. auto.
        + auto. 
      - auto.
    }
    intros [Mm | [F Mm]]. {
      (* this is when os1 \in bulletLang (shiftWith v1 mr) *)
      apply IHmr in Mm.
      2 : simpl in Hspur; tauto.
      2 : subst os1; apply ofirstn_outer_length_wf; auto.
      destruct Mm as [a Mm].
      exists a. intros v0. specialize (Mm v0).
      subst os1.
      destruct os as (w, o). simpl.
      destruct w as [ | w0 w']. { unfold olength in M1. simpl in M1. lia. }
      destruct o as [ | o0 o']. { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
      destruct o' as [ | o1 o'']. { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
      simpl in Mm. simpl.
      apply mmatch_star with (n := S (S n')); auto.
      subst os2.
      unfold oskipn in *. simpl in *. auto.
    } {
    (* this is when os1 \in stripLang mr *)
    apply finalWith_fw in F. 
    2 : simpl in Hspur; tauto.
    destruct F as [a Mleft].
    exists a. intros v0. specialize (Mleft v0).
    subst os1.
    destruct os as (w, o). simpl.
    destruct w as [ | w0 w']. { unfold olength in M1. simpl in M1. lia. }
    destruct o as [ | o0 o']. { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    destruct o' as [ | o1 o'']. { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    simpl in Mm. simpl.
    subst os2. unfold oskipn in M3. simpl in M3.
    apply mmatch_star with (n := 1); auto.
    apply omatch_star with (n := (S n')); auto.
    } 
  }
Qed.
  


Lemma nullableWith_shiftWith : forall (mr : MRegex) (v : valuation),
    nullableWith v (shiftWith v mr) = nullableWith v mr.
Proof.
  intros.
  pose proof (nullableWith_iff mr v).
  pose proof (nullableWith_iff (shiftWith v mr) v).
  rewrite shiftWith_strip in H0.
  destruct (nullableWith v mr) eqn:En;
  destruct (nullableWith v (shiftWith v mr)) eqn:En'; 
  firstorder.
Qed.

Lemma followWith_initMarkWith_shiftWith : forall (mr : MRegex) (v : valuation),
       followWith true v mr = initMarkWith v (shiftWith v mr)
    /\ followWith false v mr = shiftWith v mr.
Proof.
  induction mr; simpl; intros v; auto.
  (* Union *)
  2 : {
    split.
    - specialize (IHmr1 v). destruct IHmr1 as [IHmr1 _].
      specialize (IHmr2 v). destruct IHmr2 as [IHmr2 _].
      rewrite IHmr1. rewrite IHmr2. auto.
    - specialize (IHmr1 v). destruct IHmr1 as [_ IHmr1].
      specialize (IHmr2 v). destruct IHmr2 as [_ IHmr2].
      rewrite IHmr1. rewrite IHmr2. auto.
  }
  (* Concat *) {
    split. {
      specialize (IHmr1 v). destruct IHmr1 as [IHmr1 _].
      specialize (IHmr2 v). 
      rewrite IHmr1. f_equal.
      rewrite nullableWith_shiftWith.
      destruct (nullableWith v mr1) eqn:En.
      - rewrite orb_true_r.
        destruct IHmr2 as [IHmr2 _].
        destruct (finalWith v mr1) eqn:Ef.
        + now rewrite initMarkWith_idempotent.
        + auto.
      - rewrite orb_false_r.
        destruct (finalWith v mr1) eqn:Ef; tauto.
    } {
      specialize (IHmr1 v). destruct IHmr1 as [_ IHmr1].
      specialize (IHmr2 v). 
      rewrite IHmr1. f_equal.
      rewrite orb_false_r.
      destruct (finalWith v mr1) eqn:Ef; tauto.
    }
  }
  (* Star *) {
    specialize (IHmr v).
    split. {
      destruct IHmr as [IHmr _].
      rewrite IHmr.
      destruct (finalWith v mr) eqn:Ef.
      - rewrite initMarkWith_idempotent. auto.
      - auto. 
    } {
      destruct (finalWith v mr) eqn:Ef.
      - destruct IHmr as [IHmr _].
        rewrite IHmr.
        auto.
      - destruct IHmr as [_ IHmr].
        rewrite IHmr.
        auto. 
    }
  }
Qed.

Lemma followWith_false : forall (mr : MRegex) (v : valuation),
    followWith false v mr = shiftWith v mr.
Proof.
  intros.
  pose proof (followWith_initMarkWith_shiftWith mr v) as H.
  tauto.
Qed.

Lemma followWith_true : forall (mr : MRegex) (v : valuation),
    followWith true v mr = initMarkWith v (shiftWith v mr).
Proof.
  intros.
  pose proof (followWith_initMarkWith_shiftWith mr v) as H.
  tauto.
Qed.



Lemma toMarked_strip : forall (or : @ORegex A),
    strip (toMarked or) = or.
Proof.
  induction or; simpl; congruence.
Qed.

Lemma toMarked_nullableWith_iff (or : ORegex) (v : valuation) :
  nullableWith v (toMarked or) = true <-> match_oregex or ([], [v]).
Proof.
  rewrite nullableWith_iff.
  rewrite toMarked_strip.
  tauto.
Qed.

Lemma toMarked_no_spurious_marks (or : ORegex) :
  no_spurious_marks (toMarked or).
Proof.
  induction or; simpl; auto.
Qed.

Lemma toMarked_finalWith (or : ORegex) (v : valuation) :
  finalWith v (toMarked or) = false.
Proof.
  induction or; simpl; auto.
  - rewrite IHor1. rewrite IHor2.
    auto.
  - rewrite IHor1. rewrite IHor2.
    auto.
Qed.

Lemma shiftWith_toMarked : forall (or : ORegex) (v : valuation),
    shiftWith v (toMarked or) = toMarked or.
Proof.
  intros or v; induction or; simpl; try congruence. auto.
  - rewrite IHor1. rewrite IHor2. auto.
    now rewrite toMarked_finalWith.
  - rewrite IHor. 
    rewrite toMarked_finalWith. auto.
Qed.

Lemma mmatch_toMarked_never : forall (or : ORegex) (os : @ostring A),
  ~ match_mregex (toMarked or) os.
Proof.
  induction or; simpl; intros os H; inversion H; subst; firstorder.
Qed.

Lemma consume_cons (or : ORegex) (a0 : A) (v0 : valuation)
  (w : list A) (o : list valuation) :
  outer_length_wf (w, o)
  -> consume or (a0 :: w, v0 :: o) = 
      consumeAux (followWith true v0 (toMarked or)) (a0 :: w) o.
Proof.
  intros Hwf.
  unfold consume. auto.
Qed.

Lemma consumeAux_cons (mr : MRegex) (a0 : A) (v0 : valuation)
  (w : list A) (o : list valuation) :
  outer_length_wf (w, o)
  -> consumeAux mr (a0 :: w) (v0 :: o) = 
      consumeAux (followWith false v0 (read a0 mr)) w o.
Proof.
  intros Hwf.
  unfold consumeAux. auto.
Qed.


Lemma consumeAux_snoc (mr : MRegex) (w : list A) (o : list valuation) 
  (a' : A) (v' : valuation) :
  length w = length o
  -> consumeAux mr (w ++ [a']) (o ++ [v']) = 
      followWith false v' (read a' (consumeAux mr w o)).
Proof.
  remember (length w) as n eqn:Hn.
  revert n mr w o v' a' Hn.
  induction n.
  - intros mr w o v' a' Hlen Heq.
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

Lemma consume_snoc (or : ORegex) 
  (w : list A) (o : list valuation) (a' : A) (v' : valuation) :
  outer_length_wf (w, o)
  -> consume or (w ++ [a'], o ++ [v']) = 
      followWith false v' (read a' (consume or (w, o))).
Proof.
  intros Hwf.
  unfold consume. simpl.
  unfold outer_length_wf in Hwf.
  destruct o as [ | o0 o']. {  simpl in Hwf. lia. }
  simpl.
  rewrite consumeAux_snoc. auto.
  simpl in Hwf. lia.
Qed.

(*

  We want a series of lemmas characterizing the behavior of consume

  - Characteristics of consume or ([], [v0])
  - Characteristics of consume or os, where os is a well-formed ostring
  - Characteristics of read a (consume or os)
*)

Lemma consume_O_fw (or : ORegex) (v0 : valuation) :
  forall (os : @ostring A),
  outer_length_wf os
  -> olength os > 0
  -> hd_error (snd os) = Some v0
  -> match_oregex or os
  -> match_mregex (consume or ([], [v0])) os.
Proof.
  intros os Hwf Hlen H M.
  simpl.
  rewrite followWith_true.
  rewrite shiftWith_toMarked.
  apply stripLang_in_initMarkWith; auto.
  rewrite toMarked_strip. auto.
Qed.

Lemma consume_O_bw (or : ORegex) (v0 : valuation) :
  forall (os : @ostring A),
  outer_length_wf os
  -> match_mregex (consume or ([], [v0])) os
  -> match_oregex or (fst os, v0 :: tl (snd os)).
Proof.
  intros os Hwf M.
  simpl in M.
  rewrite followWith_true in M.
  rewrite shiftWith_toMarked in M.
  apply initMarkWith_bw in M; auto.
  destruct M as [_ [ M | M]].
  - rewrite toMarked_strip in M. auto.
  - apply mmatch_toMarked_never in M. contradiction.
Qed.

Lemma consume_fw_aux :
  forall (os_left : ostring),
  outer_length_wf os_left
  -> (
    forall (or : ORegex) (os : ostring),
    outer_length_wf os
    -> olength os > olength os_left
    -> match_oregex or os
    -> ofirstn (olength os_left) os = os_left
    -> match_mregex (consume or os_left) (oskipn (olength os_left) os)
  ) /\ (
    forall (or : ORegex) (os : ostring) (a : A),
    outer_length_wf os
    -> olength os > olength os_left
    -> match_oregex or os
    -> ofirstn (olength os_left) os = os_left
    -> hd_error (fst (oskipn (olength os_left) os)) = Some a
    -> match_mregex (read a (consume or os_left)) (oskipn (olength os_left) os)
  ).
Proof.
  apply ostring_rev_ind. (* this is induction on os_left *) {
    (* when os_left is of length 0 *)
    intros. split. {
      intros. destruct os as (w, o).
      apply consume_O_fw; auto.
      unfold olength in *. simpl in *.
      unfold ofirstn in H2. simpl in H2.
      destruct o; now inversion H2.
    } {
      intros. destruct os as (w, o).
      pose proof (consume_O_fw or v0 (w, o) H H0).
      assert ( hd_error (snd (w, o)) = Some v0) as Hhd. {
        unfold olength, ofirstn in *. simpl in *.
        destruct o; now inversion H2.
      }
      specialize (H4 Hhd H1).
      apply read_fw with (a := a) in H4; auto.
    }
  } {
  intros. split. {
    (* consume case *)
  destruct H0 as [IHconsume IHread].
  intros or os Hwf Hlen M Hagree.
  rewrite consume_snoc; [ | assumption].
  rewrite followWith_false.
  replace ((oskipn (olength (w ++ [a], o ++ [v])) os))
    with (oskipn 1 (oskipn (olength (w, o)) os)).
  2 : {
    unfold olength. simpl.
    rewrite app_length. simpl.
    rewrite oskipn_oskipn. f_equal.
    lia.
  }
  apply shiftWith_fw.
  { auto using oskipn_outer_length_wf. }
  { rewrite oskipn_olength. unfold olength in Hlen. unfold olength. simpl. simpl in Hlen.
    rewrite app_length in Hlen. simpl in Hlen. lia. }
  { clear IHconsume IHread. unfold olength in *. simpl in *.
    destruct os as (w', o').
    unfold ofirstn in Hagree.
    rewrite app_length in *. simpl length in *.
    simpl fst in *. simpl snd in *.
    rewrite <- skipn_tl. rewrite skipn_skipn.
    replace (min (length w) (length w')) with (length w) by lia.
    remember (S (length w + 1)) as n.
    inversion Hagree. rewrite <- firstn_skipn with (l := o') (n := n).
    rewrite skipn_app.
    rewrite H2. rewrite skipn_app.
    unfold outer_length_wf in Hwf. simpl in Hwf.
    apply f_equal with (f := @length valuation) in H2.
    rewrite firstn_length in H2. rewrite app_length in H2. simpl in H2.
    rewrite skipn_all2 by lia.
    replace (1 + length w - length o) with 0 by lia.
    auto. 
  }
  apply IHread; auto.
  { unfold olength in *. simpl in *.
    rewrite app_length in *. simpl in *.
    lia. }
  { remember (olength (w, o)) as n eqn:Hn.
    assert (olength (w ++ [a], o ++ [v]) = S n) as Hlen'. {
      unfold olength in *. simpl in *. rewrite app_length. simpl. lia.
    }
    rewrite Hlen' in Hagree.
    replace (ofirstn n os) with (ofirstn n (ofirstn ( S n) os)).
    2: { rewrite ofirstn_ofirstn. f_equal. lia. }
    rewrite Hagree. unfold ofirstn in *.
    remember (S n) as n1. remember (S n1) as n2.
    simpl.
    inversion Hagree. rewrite H1. rewrite H2.
    unfold olength in Hn. simpl in Hn.
    unfold outer_length_wf in H. simpl in H.
    rewrite firstn_app. rewrite firstn_app.
    replace (n - length w) with 0 by lia.
    replace (n1 - length o) with 0 by lia.
    simpl. repeat rewrite firstn_all2 by lia.
    now autorewrite with list. 
  }{
    clear IHread IHconsume.
    destruct os as (w', o'). 
    unfold olength in *. simpl in *.
    unfold outer_length_wf in Hwf, H. simpl in Hwf, H.
    rewrite app_length in Hlen. simpl in Hlen.
    rewrite app_length in Hagree. simpl in Hagree.
    unfold ofirstn in Hagree. simpl in Hagree.
    inversion Hagree. clear Hagree H2.
    rewrite <- firstn_skipn with (n := length w + 1) (l := w').
    rewrite skipn_app. rewrite H1. rewrite skipn_app.
    rewrite skipn_all. replace (length w - length w) with 0 by lia.
    auto.
  }
  }{
    (* read case *)
  destruct H0 as [IHconsume IHread].
  intros or os a0 Hwf Hlen M Hagree Hhd.
  rewrite consume_snoc; [ | assumption].
  rewrite followWith_false.
  replace ((oskipn (olength (w ++ [a], o ++ [v])) os))
    with (oskipn 1 (oskipn (olength (w, o)) os)).
  2 : {
    unfold olength. simpl.
    rewrite app_length. simpl.
    rewrite oskipn_oskipn. f_equal.
    lia.
  }
  apply read_fw.
  { auto using oskipn_outer_length_wf. }
  2 : { 
    destruct os as (w', o'). clear IHconsume IHread.
    unfold olength in *. simpl length in *.
    unfold outer_length_wf in Hwf, H. simpl in Hwf, H.
    rewrite app_length in Hlen. simpl in Hlen.
    rewrite app_length in Hagree. simpl in Hagree.
    unfold ofirstn in Hagree. simpl in Hagree.
    inversion Hagree. clear Hagree H2.
    rewrite oskipn_oskipn. remember (1 + length w) as n.
    unfold oskipn in *. simpl in *.
    rewrite app_length in Hhd. simpl in Hhd.
    rewrite <- Hhd. f_equal. f_equal. lia.
   }
  apply shiftWith_fw.
  { auto using oskipn_outer_length_wf. }
  { rewrite oskipn_olength. unfold olength in Hlen. unfold olength. simpl. simpl in Hlen.
    rewrite app_length in Hlen. simpl in Hlen. lia. }
  { clear IHconsume IHread. unfold olength in *. simpl in *.
    destruct os as (w', o').
    unfold ofirstn in Hagree.
    rewrite app_length in *. simpl length in *.
    simpl fst in *. simpl snd in *.
    rewrite <- skipn_tl. rewrite skipn_skipn.
    replace (min (length w) (length w')) with (length w) by lia.
    remember (S (length w + 1)) as n.
    inversion Hagree. rewrite <- firstn_skipn with (l := o') (n := n).
    rewrite skipn_app.
    rewrite H2. rewrite skipn_app.
    unfold outer_length_wf in Hwf. simpl in Hwf.
    apply f_equal with (f := @length valuation) in H2.
    rewrite firstn_length in H2. rewrite app_length in H2. simpl in H2.
    rewrite skipn_all2 by lia.
    replace (1 + length w - length o) with 0 by lia.
    auto. 
  } 
  apply read_fw.
  { auto using oskipn_outer_length_wf. }
  2 : {
    destruct os as (w', o').
    clear IHconsume IHread. unfold olength in *. simpl in *.
    unfold outer_length_wf in Hwf, H. simpl in Hwf, H.
    unfold ofirstn in Hagree. simpl in Hagree.
    inversion Hagree. clear Hagree H2.
    rewrite app_length in H1. simpl in H1.
    rewrite <- firstn_skipn with (n := length w + 1) (l := w').
    rewrite skipn_app. rewrite H1. rewrite skipn_app.
    rewrite skipn_all. replace (length w - length w) with 0 by lia.
    auto.
  }
  apply IHconsume; auto.
  { unfold olength in *. simpl length in *. rewrite app_length in Hlen. simpl in Hlen. lia. }
  { clear IHconsume IHread. 
    destruct os as (w', o'). 
    unfold olength in *. simpl in *.
    rewrite app_length in *. simpl in *.
    unfold ofirstn in *. remember (S (length w + 1)) as n.
    inversion Hagree. clear Hagree.
    simpl fst. simpl snd.
    f_equal.
    - rewrite <- firstn_skipn with (l := w') (n := length w + 1).
      rewrite firstn_app.
      rewrite firstn_length.
      replace (length w - min (length w + 1) (length w')) with 0 by lia.
      rewrite firstn_O.
      rewrite H1. rewrite firstn_app.
      replace (length w - length w) with 0 by lia.
      rewrite firstn_all. now autorewrite with list.
    - rewrite <- firstn_skipn with (l := o') (n := n).
      rewrite firstn_app.
      rewrite firstn_length.
      unfold outer_length_wf in *. simpl in H, Hwf.
      replace (S (length w) - Nat.min n (length o')) with 0 by lia.
      rewrite firstn_O.
      rewrite H2. rewrite firstn_app.
      replace (S (length w) - length o) with 0 by lia.
      rewrite firstn_all2. 2 : lia.
      rewrite firstn_O. now autorewrite with list.
  }
  } } 
Qed.

Lemma consume_fw (os_left : ostring) (or : ORegex) (os : ostring) :
  outer_length_wf os_left
  -> outer_length_wf os
  -> olength os > olength os_left
  -> match_oregex or os
  -> ofirstn (olength os_left) os = os_left
  -> match_mregex (consume or os_left) (oskipn (olength os_left) os).
Proof.
  intros Hwf Hwf' Hlen M Hagree.
  pose proof (consume_fw_aux os_left Hwf).
  destruct H as [Hconsume _].
  apply Hconsume; auto.
Qed.

Lemma consume_read_fw (os_left : ostring) (or : ORegex) (os : ostring) (a : A) :
  outer_length_wf os_left
  -> outer_length_wf os
  -> olength os > olength os_left
  -> match_oregex or os
  -> ofirstn (olength os_left) os = os_left
  -> hd_error (fst (oskipn (olength os_left) os)) = Some a
  -> match_mregex (read a (consume or os_left)) (oskipn (olength os_left) os).
Proof.
  intros Hwf Hwf' Hlen M Hagree Hhd.
  pose proof (consume_fw_aux os_left Hwf).
  destruct H as [_ Hread].
  apply Hread; auto.
Qed.

Lemma consume_bw_aux : forall (os_left : ostring),
  outer_length_wf os_left
  -> (
    forall (or : ORegex) (os_right : ostring),
    outer_length_wf os_right
    -> match_mregex (consume or os_left) os_right
    -> match_oregex or (fst os_left ++ fst os_right, snd os_left ++ tl (snd os_right))
  ) /\ (
    forall (or : ORegex) (os_right : ostring) (a : A),
    outer_length_wf os_right
    -> olength os_right > 0
    -> match_mregex (read a (consume or os_left)) os_right
    -> match_oregex or (fst os_left ++ [a] ++ tl (fst os_right), snd os_left ++ tl (snd os_right))
  ).
Proof.
  apply ostring_rev_ind. { (* the induction is on os_left *)
    (* when olength (os_left) = 0 *)
    intros. split. {
      intros ? ? Hwf M.
      apply consume_O_bw in M; auto.
    } {
      intros ? ? ? Hwf ? M.
      pose proof (mmatch_no_empty_strings _ _ M).
      destruct os_right as (wR, oR).
      unfold olength in H. simpl in H.
      destruct oR as [ | o0 oR'].  { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
      destruct wR as [ | w0 wR']. { unfold olength in H. simpl in H. lia. }
      simpl.
      apply read_bw in M; [ | assumption].
      simpl in M.
      rewrite followWith_true in M.
      rewrite shiftWith_toMarked in M.
      apply initMarkWith_bw in M.
      2 : { unfold outer_length_wf in *. simpl in *. lia. }
      simpl in M. rewrite toMarked_strip in M.
      destruct M as [_ [M | M]].
      - auto. 
      - apply mmatch_toMarked_never in M. contradiction.
    }
  } {
  intros ? ? wL oL HwfL [IHconsume IHread]. split. {
    (* consume case *)
    intros ? ? HwfR M.
    rewrite consume_snoc in M; [ | assumption].
    rewrite followWith_false in M.
    apply shiftWith_bw in M.
    3 : { auto using oskipn_outer_length_wf. }
    2 : { apply read_no_spurious. }
    destruct M as [a0 M].
    destruct (unsnoc oL) as [[oL' vL] | ]eqn:EoL.
    2 : { apply unsnoc_None in EoL. subst oL. unfold outer_length_wf in HwfL.
          simpl in HwfL. lia. }
    apply unsnoc_Some in EoL.
    specialize (M vL).
    apply IHread in M.
    2 : { unfold outer_length_wf in HwfL |- *. simpl in HwfL |- *.
    destruct os_right as (wR, oR).
    unfold outer_length_wf in HwfR. simpl in HwfR.
    destruct oR as [ | o0 oR']. { simpl in HwfR. lia. }
    simpl. simpl in HwfR. lia. }
    2 : { unfold olength. simpl. lia. }
    simpl in M. simpl.
    repeat rewrite <- app_assoc. simpl. auto.
  }
  { (* read case *)
    intros ? ? a0 HwfR HlenR M.
    rewrite consume_snoc in M; [ | assumption].
    rewrite followWith_false in M.
    apply read_bw in M; [ | assumption].
    apply shiftWith_bw in M.
    3 : { 
      destruct os_right as (wR, oR).
      unfold outer_length_wf in HwfR |- *. simpl in HwfR |- *.
      destruct oR as [ | o0 oR']. { simpl in HwfR. lia. }
      destruct wR as [ | w0 wR']. { unfold olength in HlenR. simpl in HlenR. lia. }
      simpl. simpl in HwfR. lia.
    }
    2 : apply read_no_spurious.
    destruct M as [a' M].
    destruct (unsnoc oL) as [[oL' vL] | ]eqn:EoL.
    2 : { apply unsnoc_None in EoL. subst oL. unfold outer_length_wf in HwfL.
          simpl in HwfL. lia. }
    apply unsnoc_Some in EoL.
    specialize (M vL). simpl fst in M. simpl snd in M.
    apply IHread in M.
    3 : { unfold olength. simpl. lia. }
    2 : { 
      destruct os_right as (wR, oR).
      unfold outer_length_wf in HwfR |- *. simpl in HwfR |- *.
      destruct oR as [ | o0 oR']. { simpl in HwfR. lia. }
      destruct wR as [ | w0 wR']. { unfold olength in HlenR. simpl in HlenR. lia. }
      simpl. simpl in HwfR. lia.
     }
    simpl in M |- *. repeat rewrite <- app_assoc; simpl. auto.
  }
  }
Qed.

Lemma consume_bw (os_left : ostring) (or : ORegex) (os_right : ostring) :
  outer_length_wf os_left
  -> outer_length_wf os_right
  -> match_mregex (consume or os_left) os_right
  -> match_oregex or (fst os_left ++ fst os_right, snd os_left ++ tl (snd os_right)).
Proof.
  intros HwfL HwfR M.
  pose proof (consume_bw_aux os_left HwfL).
  destruct H as [Hconsume _].
  apply Hconsume; auto.
Qed.

Lemma consume_read_bw (os_left : ostring) (or : ORegex) (os_right : ostring) (a : A) :
  outer_length_wf os_left
  -> outer_length_wf os_right
  -> olength os_right > 0
  -> match_mregex (read a (consume or os_left)) os_right
  -> match_oregex or (fst os_left ++ [a] ++ tl (fst os_right), snd os_left ++ tl (snd os_right)).
Proof.
  intros HwfL HwfR HlenR M.
  pose proof (consume_bw_aux os_left HwfL).
  destruct H as [_ Hread].
  apply Hread; auto.
Qed.

Lemma membership_nonempty (or : ORegex) (os : @ostring A) (a' : A) (v' : valuation) :
  outer_length_wf os
  -> finalWith v' (read a' (consume or os)) = true
  <-> match_oregex or (fst os ++ [a'], snd os ++ [v']).
Proof.
  intros Hwf. destruct os as (w, o).
  split. {
    intros H.
    apply finalWith_fw in H; [ | apply read_no_spurious].
    destruct H as [a M].
    destruct (unsnoc o) as [[o' v0] | ] eqn:Eo.
    2 : { apply unsnoc_None in Eo. subst o. unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    apply unsnoc_Some in Eo.
    specialize (M v0).
    apply consume_read_bw in M; auto.
    unfold outer_length_wf. auto. 
  } {
    intros H.
    simpl in H.
    destruct (unsnoc o) as [[o' v0] | ] eqn:Eo.
    2 : { apply unsnoc_None in Eo. subst o. unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
    apply unsnoc_Some in Eo.
    apply finalWith_bw with (v0 := v0) (a := a').
    pose proof (consume_read_fw (w, o) or (w ++ [a'], o ++ [v']) a' Hwf).
    assert (olength (w ++ [a'], o ++ [v']) > olength (w, o)) as Hlen_gt. {
      unfold olength. simpl. rewrite app_length. simpl. lia.
    }
    assert (outer_length_wf (w ++ [a'], o ++ [v'])) as Hwf'. {
      unfold outer_length_wf in Hwf |- *. simpl in *. repeat rewrite app_length. simpl. lia.
    }
    assert (ofirstn (olength (w, o)) (w ++ [a'], o ++ [v']) = (w, o)) as Hagree. {
      unfold ofirstn. simpl fst. simpl snd.
      unfold olength. simpl fst.
      remember (S (length w)) as n.
      f_equal.
      - rewrite firstn_app.
        rewrite firstn_all. 
        replace (length w - length w) with 0 by lia.
        now autorewrite with list.
      - rewrite firstn_app.
        unfold outer_length_wf in Hwf. simpl in Hwf.
        replace (n - length o) with 0 by lia.
        rewrite firstn_all2. 2 : lia.
        now autorewrite with list.
    }
    assert (hd_error (fst (oskipn (olength (w, o)) (w ++ [a'], o ++ [v']))) =
    Some a') as Hhd. {
      unfold oskipn, olength. simpl. 
      rewrite skipn_app.
      rewrite skipn_all2. 2 : lia.
      replace (length w - length w) with 0 by lia.
      auto.
    }
    specialize (H0 Hwf' Hlen_gt H Hagree Hhd).
    assert ((oskipn (olength (w, o)) (w ++ [a'], o ++ [v'])) = ([a'], [v0; v'])) as Hoskipn. {
      unfold oskipn, olength. simpl. rewrite skipn_app. rewrite skipn_all2. 2 : lia.
      replace (length w - length w) with 0 by lia.
      simpl. f_equal.
      rewrite app_length. simpl.
      replace (min (length w) (length w + 1)) with (length w) by lia.
      rewrite Eo. rewrite <- app_assoc.
      simpl. 
      rewrite skipn_app. unfold outer_length_wf in Hwf. simpl in Hwf.
      assert (1 + length o' = length o). {
        rewrite Eo. simpl. rewrite app_length. simpl. lia.
      }
      rewrite skipn_all2. 2 : lia.
      replace (length w - length o') with 0 by lia.
      auto.
    }
    rewrite Hoskipn in H0.
    apply H0.
  }
Qed.




Lemma matcherStatesAux_snoc (mr : MRegex) (w : list A) (o : list valuation) 
  (a' : A) (v' : valuation) :
  length w = length o
  -> matcherStatesAux mr (w ++ [a']) (o ++ [v']) = 
      matcherStatesAux mr w o ++ 
      match last_error (matcherStatesAux mr w o) with
      | Some (_, m) => [(finalWith v' (read a' m), followWith false v' (read a' m))]
      | None => [(finalWith v' (read a' mr), followWith false v' (read a' mr))]
      end.
Proof.
  remember (length w) as n eqn:Hn.
  revert n mr w o v' a' Hn.
  induction n.
  - intros mr w o v' a' Hlen Heq.
    destruct w as [ | w0 w']. 2 : { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. 2 : { simpl in Heq. lia. }
    simpl. auto.
  - intros mr w o v' a' Hlen Heq.
    destruct w as [ | w0 w']. { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. { simpl in Heq. lia. }
    simpl in Hlen. simpl in Heq.
    simpl. rewrite IHn. 2, 3: lia.
    f_equal. f_equal.
    remember (matcherStatesAux _ _ _) as ms.
    destruct ms as [ | m ms'].
    + simpl. auto.
    + rewrite last_error_cons_cons.
      destruct (last_error (m :: ms')) eqn:Ems; [auto| ].
      rewrite last_error_None in Ems.
      discriminate.
Qed.

Lemma matcherStatesAux_cons (mr : MRegex) (a : A) (v : valuation) (w : list A) (o : list valuation) :
  matcherStatesAux mr (a :: w) (v :: o) = 
    (finalWith v (read a mr), followWith false v (read a mr)) :: 
    matcherStatesAux (followWith false v (read a mr)) w o.
Proof.
  auto. 
Qed.

Lemma matcherStatesAux_app (mr : MRegex) (wL wR : list A) (oL oR : list valuation) :
  length wL = length oL
  -> matcherStatesAux mr (wL ++ wR) (oL ++ oR) = 
      matcherStatesAux mr wL oL ++ 
      match last_error (matcherStatesAux mr wL oL) with
      | Some (_, m) => matcherStatesAux m wR oR
      | None => matcherStatesAux mr wR oR
      end.
Proof.
  remember (length wL) as n eqn:Hn.
  revert n mr wL oL wR oR Hn.
  induction n.
  - intros mr wL oL wR oR Hlen1 Hlen2.
    destruct wL as [ | w0 wL]. 2 : { simpl in Hlen1. lia. }
    destruct oL as [ | o0 oL]. 2 : { simpl in Hlen2. lia. }
    simpl. auto.
  - intros mr wL oL wR oR Hlen1 Hlen2.
    destruct wL as [ | w0 wL]. { simpl in Hlen1. lia. }
    destruct oL as [ | o0 oL]. { simpl in Hlen2. lia. }
    simpl in Hlen1, Hlen2.
    simpl. rewrite IHn. 2, 3: lia.
    f_equal. f_equal.
    remember (matcherStatesAux _ _ _) as ms.
    destruct ms as [ | m ms'].
    + simpl. auto.
    + rewrite last_error_cons_cons.
      destruct (last_error (m :: ms')) eqn:Ems; [auto| ].
      rewrite last_error_None in Ems.
      discriminate.
Qed. 

Lemma matcherStates_non_empty (or : ORegex) (w : list A) (o : list valuation) :
  outer_length_wf (w, o)
  -> matcherStates or (w, o) <> [].
Proof.
  intros Hwf.
  destruct o as [ | o0 o']. { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
  simpl. discriminate.
Qed.

Lemma matcherStates_snoc (or : ORegex) (w : list A) (o : list valuation) (a' : A) (v' : valuation) :
  outer_length_wf (w, o)
  -> matcherStates or (w ++ [a'], o ++ [v']) = 
      matcherStates or (w, o) ++ 
      match last_error (matcherStates or (w, o)) with
      | Some (_, m) => [(finalWith v' (read a' m), followWith false v' (read a' m))]
      | None => [] (* shouldn't arise! *)
      end.
Proof.
  intros Hwf.
  unfold outer_length_wf in Hwf.
  simpl in Hwf.
  destruct o as [ | o0 o']. { simpl in Hwf. lia. }
  pose proof (matcherStates_non_empty or w (o0 :: o') ltac:(auto)).
  destruct (last_error (matcherStates or (w, o0 :: o'))) as [[ls s] | ] eqn:E.
  2 : { rewrite last_error_None in E. contradiction. }
  rewrite last_error_Some in E.
  destruct E as [l' E].
  unfold matcherStates. simpl in Hwf |- *.
  f_equal.
  rewrite matcherStatesAux_snoc. 2 : lia.
  f_equal.
  simpl in E.
  destruct w as [ | w0 w']. {
    destruct o' as [ | o0' o'']. 2 : { simpl in Hwf. lia. }
    simpl in E |- *.
    destruct l' as [ | l0 l']. 2 : { 
      apply f_equal with (f := @length _) in E. 
      simpl in E. rewrite app_length in E. simpl in E. lia.
    }
    simpl in E. inversion E. auto.
  }
  destruct o' as [ | o0' o'']. { simpl in Hwf. lia. }
  remember (last_error (matcherStatesAux _ _ _)) as l.
  destruct l as [[lss s'] | ]. 2 : { 
    simpl in Heql. symmetry in Heql. apply last_error_None in Heql.
    discriminate.
  }
  symmetry in Heql.
  rewrite last_error_Some in Heql.
  destruct Heql as [l'' Heql].
  rewrite Heql in E.
  replace ((nullableWith o0 (toMarked or), followWith true o0 (toMarked or)) :: l'' ++ [(lss, s')])
    with (((nullableWith o0 (toMarked or), followWith true o0 (toMarked or)) :: l'') ++ [(lss, s')]) in E by auto.
  apply last_inversion in E.
  destruct E as [_ E2]. inversion E2. auto.
Qed.



Lemma matcherStates_consume_last_error : forall (os : ostring) (Hwf : outer_length_wf os) 
    (or : ORegex) (a' : A) (v' : valuation),
  last_error (matcherStates or (fst os ++ [a'], snd os ++ [v'])) =
      Some (finalWith v' (read a' (consume or os)), followWith false v' (read a' (consume or os))).
Proof.
  pose (fun os => forall (or : ORegex) (a' : A) (v' : valuation),
  last_error (matcherStates or (fst os ++ [a'], snd os ++ [v'])) =
  Some (finalWith v' (read a' (consume or os)), followWith false v' (read a' (consume or os)))).
  enough (forall os, outer_length_wf os -> P os) as H.
  { intros. apply H; auto. }
  apply ostring_rev_ind; subst P.
  - simpl. intros. auto.
  - intros ? ? ? ? Hwf IH ? ? ?.
    cbv beta in IH |- *.
    simpl fst in *. simpl snd in *.
    rewrite matcherStates_snoc. 2 : {
      unfold outer_length_wf in Hwf |- *. simpl in Hwf |- *.
      repeat rewrite app_length. simpl. lia.
    }
    rewrite IH.
    rewrite consume_snoc. 2 : { auto. }
    rewrite last_error_snoc. auto.
Qed.

Lemma matcherStates_consume_last_error_2 : forall (os : ostring) (Hwf : outer_length_wf os) 
    (or : ORegex) (a' : A) (v' : valuation),
  last_error (matcherStates or (fst os ++ [a'], snd os ++ [v'])) =
      Some (finalWith v' (read a' (consume or os)), consume or (fst os ++ [a'], snd os ++ [v'])).
Proof.
  intros. 
  rewrite matcherStates_consume_last_error; [ | auto].
  rewrite consume_snoc; [ | auto].
  repeat f_equal. destruct os. auto.
Qed.

Lemma matcherStates_consume (or : ORegex) (os : ostring) (Hwf : outer_length_wf os) :
  olength os > 0
  -> option_map snd (last_error (matcherStates or os)) = 
      Some (consume or os).
Proof.
  revert or Hwf.
  remember (olength os) as n eqn:Hn.
  revert os Hn.
  induction n using lt_wf_ind.
  intros os Hlen1 or Hwf Hlen.
  subst n.
  destruct os as (w, o).
  destruct (unsnoc w) as [[w' a'] | ] eqn:Ew.
  2 : { apply unsnoc_None in Ew. subst w.
  unfold olength in Hlen. simpl in Hlen. lia. }
  rewrite unsnoc_Some in Ew.
  destruct (unsnoc o) as [[o' v] | ] eqn:Eo.
  2 : { apply unsnoc_None in Eo. subst o. 
  unfold olength in Hlen. unfold outer_length_wf in Hwf.
  simpl in Hwf. simpl in Hlen. lia. }
  apply unsnoc_Some in Eo.
  rewrite Ew. rewrite Eo.
  assert (outer_length_wf (w', o')) as Hwf'. { 
    unfold outer_length_wf in *. simpl in *.
    subst. repeat rewrite app_length in Hwf. simpl in Hwf. lia.
  }
  rewrite matcherStates_snoc. 2 : auto.
  destruct (last_error (matcherStates or (w', o'))) as [[b m] | ] eqn:E.
  2 : { apply last_error_None in E. 
  pose proof (matcherStates_non_empty or w' o' Hwf').
  contradiction. }
  rewrite last_error_snoc. simpl option_map.
  rewrite consume_snoc. 2 : assumption.
  enough (consume or (w', o') = m) as HHH. { rewrite HHH. auto. }
  destruct w' as [ | w1 w']. {
    destruct o' as [ | o1 o']. {
      unfold outer_length_wf in Hwf'. simpl in Hwf'. lia.
    }
    destruct o' as [ | o2 o']. 2 : { 
      unfold outer_length_wf in Hwf'. simpl in Hwf'. lia. }
    simpl in E |- *.
    unfold last_error in E. simpl in E.
    inversion E. auto.
  }
  assert (Some m = option_map snd (Some (b, m))) as HH by auto.
  rewrite <- E in HH.
  rewrite H with (m := (olength (w, o)) - 1) in HH; 
   try unfold olength in *; unfold outer_length_wf in *.
  inversion HH. auto.
  - subst w. simpl. lia.
  - simpl in Hwf' |- *. subst w. 
    rewrite app_length. simpl. lia.
  - simpl in Hwf' |- *. auto.
  - subst w. simpl. rewrite app_length. simpl. lia.
Qed. 

  

Lemma matcherStates_app (or : ORegex) (wL wR : list A) (oL oR : list valuation) :
  outer_length_wf (wL, oL)
  -> length wR = length oR
  -> matcherStates or (wL ++ wR, oL ++ oR) = 
      matcherStates or (wL, oL) ++ 
      matcherStatesAux (consume or (wL, oL)) wR oR.
Proof.
  intros Hwf Hlen.
  destruct oL as [ | v0 oL]. { 
    unfold outer_length_wf in Hwf. 
    simpl in Hwf. lia. 
  }
  simpl matcherStates at 1.
  assert (length wL = length oL) as Hlen'. {
    unfold outer_length_wf in Hwf. simpl in Hwf. lia.
  }
  rewrite matcherStatesAux_app. 2 : auto.
  (* when |wL| = |oL| = 0 *)
  destruct wL as [ | w0 wL'] eqn:EwL. {
    destruct oL as [ | o0 oL'] eqn:EoL. 2: {
      simpl in Hlen'. lia.
    }
    simpl. auto.
  }
  destruct oL as [ | o0' oL'] eqn:EoL. { simpl in Hlen'. lia. }
  (* when |wL| = |oL| > 0 *)
  rewrite <- EwL. rewrite <- EoL.
  assert (
    (nullableWith v0 (toMarked or), followWith true v0 (toMarked or))
  :: matcherStatesAux (followWith true v0 (toMarked or)) wL oL
  = matcherStates or (wL, v0 :: oL)
  ) as HL by auto. 
  assert (
    last_error (matcherStatesAux (followWith true v0 (toMarked or)) wL oL)
    = last_error ((nullableWith v0 (toMarked or), followWith true v0 (toMarked or))
    :: matcherStatesAux (followWith true v0 (toMarked or)) wL oL)
  ) as X.
  { subst. simpl. rewrite last_error_cons_cons. auto. }
  rewrite X. rewrite HL.
  destruct (last_error (matcherStates or (wL, v0 :: oL)))
  as [[b m] | ] eqn:E.
  2 : {  apply last_error_None in E. rewrite <- HL. discriminate. }
  assert (outer_length_wf (wL, v0 :: oL)). {
    unfold outer_length_wf in Hwf |- *. simpl in Hwf |- *.
    subst. simpl in Hwf |- *. lia.
  }
  assert (olength (wL, v0 :: oL) > 0) as Hlen_gt. {
    unfold olength. simpl. subst. simpl. lia.
  }
  pose proof (matcherStates_consume or (wL, v0 :: oL) H Hlen_gt).
  rewrite E in H0. simpl in H0.
  inversion H0.
  auto.
Qed.

Lemma matcherStatesAux_length (mr : MRegex) (w : list A) (o : list valuation) :
  length w = length o
  -> length (matcherStatesAux mr w o) = length w.
Proof.
  remember (length w) as n eqn:Hn.
  revert n mr w o Hn.
  induction n.
  - intros mr w o Hlen Hlen'. destruct w as [ | w0 w']. 2 : { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. 2 : { simpl in Hlen'. lia. }
    simpl. auto.
  - intros mr w o Hlen Hlen'.
    destruct w as [ | w0 w']. { simpl in Hlen. lia. }
    destruct o as [ | o0 o']. { simpl in Hlen'. lia. }
    simpl in Hlen, Hlen'.
    simpl. f_equal. apply IHn. lia. lia.
Qed.

Lemma matcherStates_length (or : ORegex) (os : @ostring A) :
  outer_length_wf os
  -> length (matcherStates or os) = olength os + 1.
Proof.
  intros Hwf.
  destruct os as (w, o).
  destruct o as [ | o0 o']. { 
    unfold outer_length_wf in Hwf. 
    simpl in Hwf. lia. 
  }
  simpl.
  assert (length w = length o') as Hlen. {
    unfold outer_length_wf in Hwf. simpl in Hwf. lia.
  }
  rewrite matcherStatesAux_length. 2 : auto.
  unfold olength. simpl. lia.
Qed.
  
Lemma matcherStates_nth_error_snd (os : ostring) (Hwf : outer_length_wf os) 
    (or : ORegex) :
  forall n, n <= olength os
  -> option_map (snd) (nth_error (matcherStates or os) n) = 
      Some (consume or (ofirstn n os)).
Proof.
  intros n Hn.
  destruct os as (w, o).
  assert (w = firstn n w ++ skipn n w) as SplitW.
  { rewrite firstn_skipn. auto. }
  destruct o as [ | o0 o']. { 
    unfold outer_length_wf in Hwf. 
    simpl in Hwf. lia. 
  }
  assert (o' = firstn n o' ++ skipn n o') as SplitO.
  { rewrite firstn_skipn. auto. }
  replace (ofirstn n (w, o0 :: o')) with ((firstn n w, o0 :: firstn n o')).
  2 : {
    unfold ofirstn. auto.
  }
  assert (outer_length_wf (firstn n w, o0 :: firstn n o')) as Hwf1. {
    unfold outer_length_wf in Hwf |- *. simpl in Hwf |- *.
    repeat rewrite firstn_length. lia.
  }
  assert (length (skipn n w) = length (skipn n o')) as Hskipn_len. {
    repeat rewrite skipn_length. 
    unfold olength in Hn. simpl in Hn.
    unfold outer_length_wf in Hwf. simpl in Hwf.
    lia.
  }
  rewrite SplitW at 1. rewrite SplitO at 1.
  replace (o0 :: firstn n o' ++ skipn n o')
    with ((o0 :: firstn n o') ++ skipn n o') by auto.
  rewrite matcherStates_app. 2, 3 : auto.
  rewrite nth_error_app1. 2 : {
    rewrite matcherStates_length; [ | auto].
    unfold olength in Hn |- *. unfold outer_length_wf in Hwf. simpl in Hn, Hwf |- * .
    rewrite firstn_length. lia.
  }
  remember (matcherStates _ _) as ms.
  destruct n. {
    repeat rewrite firstn_O in Heqms |- *.
    subst ms. auto.
  }
  destruct w as [ | w0 w']. {
    unfold olength in Hn. simpl in Hn. lia.
  }
  destruct o' as [ | o1 o'']. {
    unfold outer_length_wf in Hwf. simpl in Hwf. lia.
  }
  remember ((firstn (S n) (w0 :: w'))) as ww.
  remember ((o0 :: firstn (S n) (o1 :: o''))) as oo.
  destruct (unsnoc ww) as [[ww' a'] | ] eqn:Eww.
  2 : { apply unsnoc_None in Eww.
    rewrite Eww in Heqww. simpl in Heqww. discriminate.
  }
  destruct (unsnoc oo) as [[oo' v'] | ] eqn:Eoo.
  2 : { apply unsnoc_None in Eoo.
    rewrite Eoo in Heqoo. simpl in Heqoo. discriminate.
  }
  apply unsnoc_Some in Eww. apply unsnoc_Some in Eoo.
  rewrite Eww in Heqms |- *. rewrite Eoo in Heqms |- *.
  assert (S n = length ms - 1) as L. {
    rewrite Heqms.
    rewrite matcherStates_length. 2 : {
      unfold outer_length_wf in Hwf, Hwf1 |- *. 
      simpl in Hwf, Hwf1 |- *.
      rewrite Eww in Hwf1. rewrite app_length in Hwf1 |- *.
      rewrite Eoo in Hwf1. rewrite app_length in Hwf1 |- *.
      simpl in Hwf1. simpl. lia.
    }
    unfold olength.
    simpl. rewrite app_length. simpl.
    unfold outer_length_wf in *.
    unfold olength in *.
    simpl in *.
    apply f_equal with (f := @length _) in Heqww.
    simpl in Heqww. rewrite firstn_length in Heqww.
    apply f_equal with (f := @length _) in Eww.
    simpl in Eww. rewrite app_length in Eww. simpl in Eww.
    lia.
  }
  rewrite L. repeat rewrite Heqms. 
  rewrite <- last_error_nth_error.
  replace ww' with (fst (ww', oo')) by auto.
  replace oo' with (snd (ww', oo')) by auto.
  rewrite matcherStates_consume_last_error_2. 
  2 : {
    rewrite Eww in Hwf1. rewrite Eoo in Hwf1.
    unfold outer_length_wf in Hwf1 |- *. simpl in Hwf1 |- *. 
    repeat rewrite app_length in Hwf1. simpl in Hwf1.
    lia. 
  }  
  auto.
Qed.

Lemma matcherStatesAux_next n : forall (mr : MRegex) (w : list A) (o : list valuation) (m : MRegex) a v,
  length w = length o 
  -> option_map snd (nth_error (matcherStatesAux mr w o) n) = Some m
    -> S n < length w
    -> nth_error w (S n) = Some a
    -> nth_error o (S n) = Some v
    -> nth_error (matcherStatesAux mr w o) (S n) = 
        Some (finalWith v (read a m), followWith false v (read a m)).
Proof.
  induction n.
  - intros mr w o m a v Hlen H Hlen' Hnthw Hntho.
    destruct w as [ | w0 w']. { simpl in Hlen'. lia. }
    destruct o as [ | o0 o']. { simpl in Hlen. lia. }
    simpl in H. inversion H.
    destruct w' as [ | w1 w'']. { simpl in Hnthw. discriminate. }
    destruct o' as [ | o1 o'']. { simpl in Hntho. discriminate. }
    simpl in Hnthw, Hntho. inversion Hnthw. inversion Hntho.
    auto.
  - intros mr w o m a v Hlen H Hlen' Hnthw Hntho.
    destruct w as [ | w0 w']. { simpl in Hlen'. lia. }
    destruct o as [ | o0 o']. { simpl in Hlen. lia. }
    remember (S n) as n'.
    simpl in Hnthw, Hntho.
    simpl. erewrite IHn. reflexivity. 4, 5: auto.
    { simpl in Hlen. lia. }
    2 : { simpl in Hlen'. lia. }
    simpl in H. subst n'. simpl in H. auto.
Qed.

Lemma matcherStates_next n : forall (or : ORegex) (w : list A) (o : list valuation) (m : MRegex) a v,
  outer_length_wf (w, o)
  -> option_map snd (nth_error (matcherStates or (w, o)) n) = Some m
    -> S n < olength (w, o)
    -> nth_error w n = Some a
    -> nth_error o (S n) = Some v
    -> nth_error (matcherStates or (w, o)) (S n) = 
        Some (finalWith v (read a m), followWith false v (read a m)).
Proof.
  intros or w o m a v Hwf H Hlen' Hnthw Hntho.
  destruct o as [ | o0 o']. { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
  simpl matcherStates.
  destruct n. {
    destruct w as [ | w0 w']. { simpl in Hnthw. discriminate. }
    destruct o' as [ | o1 o'']. { simpl in Hntho. discriminate. }
    simpl in H. inversion H.
    simpl.
    simpl in Hnthw, Hntho. inversion Hnthw. inversion Hntho. subst.
    auto.
  }
  remember (S n) as n'.
  simpl nth_error.
  subst n'. erewrite matcherStatesAux_next.
  reflexivity. 4: auto.
  { unfold outer_length_wf in Hwf. simpl in Hwf. lia. }
  2 : { 
    assert (nth_error w (S n) <> None) as X. {
      intros X. congruence.
    }
    rewrite nth_error_Some in X. auto.
  }
  2 : {
    remember (S n) as n'.
    now simpl in Hntho.
  }
  simpl in H. auto.
Qed.

Lemma matcherStates_nth_error_aux (w : list A) (o : list valuation) (Hwf : outer_length_wf (w, o)) 
(or : ORegex) :
  forall n, S n < olength (w, o)
  -> forall a, nth_error w n = Some a
  -> forall v, nth_error o (S n) = Some v
  -> nth_error (matcherStates or (w, o)) (S n) = 
      Some (finalWith v (read a (consume or (ofirstn n (w, o)))), 
            followWith false v (read a (consume or (ofirstn n (w, o))))).
Proof.
  intros n Hlen a Hnthw v Hntho.
  erewrite matcherStates_next; eauto.
  rewrite matcherStates_nth_error_snd; auto.
  lia.
Qed.

Lemma matcherStates_nth_error_aux2 (w : list A) (o : list valuation) (Hwf : outer_length_wf (w, o))
(or : ORegex) :
  forall n, S n < olength (w, o)
  -> option_map fst (nth_error (matcherStates or (w, o)) (S n)) = Some true
  <-> match_oregex or (ofirstn (S n) (w, o)).
Proof.
  intros n Hn.
  pose proof (matcherStates_nth_error_aux w o Hwf or n Hn).
  pose proof (nth_error_Some_ex w n) as Nw.
  pose proof (nth_error_Some_ex o (S n)) as No.
  assert (n < length w) as Lnw. {
    unfold olength in Hn. simpl in Hn. lia.
  }
  assert (S n < length o) as Lno. {
    unfold olength in Hn. simpl in Hn.
    unfold outer_length_wf in Hwf. simpl in Hwf.
    lia.
  }
  assert (LnoX := Lno). assert (LnwX := Lnw).
  apply Nw in Lnw. apply No in Lno.
  destruct Lnw as [a Hnthw].
  destruct Lno as [v Hntho].
  specialize (H a Hnthw v Hntho).
  rewrite H.
  remember (finalWith _ _) as b. simpl.
  enough (b = true <-> match_oregex or (ofirstn (S n) (w, o))) as HHH. {
    rewrite <- HHH. split; intros HSome; inversion HSome; auto.
  }
  subst b.
  rewrite membership_nonempty.
  2 : now apply ofirstn_outer_length_wf.
  enough ((fst (ofirstn n (w, o)) ++ [a], snd (ofirstn n (w, o)) ++ [v])
    = (ofirstn (S n) (w, o))) as HHH. {
    rewrite HHH. tauto.
  }
  unfold ofirstn. 
  remember (S n) as n'. remember (S n') as n''. simpl.
  f_equal.
  - rewrite <- firstn_skipn with (n := n) (l := w) at 2.
    rewrite firstn_app.
    rewrite firstn_firstn. rewrite firstn_length.
    replace (min n' n) with n by lia.
    f_equal. replace (n' - Nat.min n (length w)) with 1 by lia.
    pose proof (hd_error_skipn w n). rewrite Hnthw in H0.
    destruct (skipn n w) as [ | w0 w']. discriminate.
    simpl in H0. inversion H0. auto.
  - subst n''. 
    rewrite <- firstn_skipn with (n := n') (l := o) at 2.
    rewrite firstn_app.
    rewrite firstn_firstn. rewrite firstn_length.
    replace (min (S n') n') with n' by lia.
    f_equal. replace (S n' - Nat.min n' (length o)) with 1 by lia.
    pose proof (hd_error_skipn o n'). rewrite Hntho in H0.
    destruct (skipn n' o) as [ | o0 o']. discriminate.
    simpl in H0. inversion H0. auto.
Qed.

Lemma matcherStates_nth_error_aux3 (w : list A) (o : list valuation) (Hwf : outer_length_wf (w, o))
(or : ORegex) :
  forall n, (S n) = olength (w, o)
  -> option_map fst (nth_error (matcherStates or (w, o)) (S n)) = Some true
  <-> match_oregex or (w, o).
Proof.
  intros n Hn.
  destruct (unsnoc w) as [[w' a] | ] eqn:Ew.
  2 : { apply unsnoc_None in Ew. subst w.
    unfold olength in Hn. simpl in Hn. lia.
  }
  destruct (unsnoc o) as [[o' v] | ] eqn:Eo.
  2 : { apply unsnoc_None in Eo. subst o.
    unfold olength in Hn. simpl in Hn.
    unfold outer_length_wf in Hwf. simpl in Hwf. lia.
  }
  apply unsnoc_Some in Ew. apply unsnoc_Some in Eo.
  assert ((S n) = (length (matcherStates or (w, o)) - 1)) as Hlen. {
    rewrite matcherStates_length. 2 : auto.
    unfold olength in Hn. simpl in Hn.
    unfold olength. simpl. lia.
  }
  rewrite Hlen.
  rewrite <- last_error_nth_error.
  rewrite Ew, Eo.
  replace w' with (fst (w', o')) at 1 by auto.
  replace o' with (snd (w', o')) at 2 by auto.
  assert (outer_length_wf (w', o')) as Hwf2. {
    unfold outer_length_wf in Hwf. simpl in Hwf.
    rewrite Ew in Hwf. rewrite Eo in Hwf.
    unfold outer_length_wf. simpl.
    repeat rewrite app_length in Hwf. simpl in Hwf. lia.
  }
  rewrite matcherStates_consume_last_error_2; [ | assumption]. 
  simpl fst. simpl snd. 
  remember (finalWith _ _) as b. simpl.
  enough (b = true <-> match_oregex or (w' ++ [a], o' ++ [v])) as HHH. {
    rewrite <- HHH. split; intros HSome; inversion HSome; auto.
  }
  subst b.
  rewrite membership_nonempty; [ | auto]. simpl. tauto.
Qed.

Lemma matcherStates_nth_error_aux4 (w : list A) (o : list valuation) (Hwf : outer_length_wf (w, o))
(or : ORegex) :
  option_map fst (nth_error (matcherStates or (w, o)) 0) = Some true
  <-> match_oregex or (ofirstn 0 (w, o)).
Proof.
  unfold outer_length_wf in Hwf.
  destruct o as [ | o0 o']. { simpl in Hwf. lia. }
  simpl in Hwf. simpl.
  unfold ofirstn. simpl.
  pose proof (nullableWith_iff (toMarked or) o0) as H.
  rewrite toMarked_strip in H. rewrite <- H.
  split; intros HSome; inversion HSome; auto.
Qed.

Lemma oscanMatcher_tape (r : ORegex) (os : @ostring A) :
  outer_length_wf os
  -> (length (oscanMatcher r os) = olength os + 1) /\
    forall i,
      i <= olength os ->
      (nth_error (oscanMatcher r os) i = Some true <-> match_oregex r (ofirstn i os)) /\
      (nth_error (oscanMatcher r os) i = Some false <-> ~ match_oregex r (ofirstn i os)).
Proof.
  intros Hwf.
  split.
  { unfold oscanMatcher. rewrite map_length. apply matcherStates_length. auto. }
  intros i Hlen.
  destruct i.
  (* i is 0 *)
  { 
    (* use matcherStates_nth_error_aux4 *)
    unfold oscanMatcher.
    rewrite nth_error_map.
    destruct os as (w, o).
    destruct (nth_error (matcherStates r (w, o)) 0) as [[b m] | ] eqn:E.
    2 : { rewrite nth_error_None in E. rewrite matcherStates_length in E.
     lia. auto.
    }
    pose proof (matcherStates_nth_error_aux4 w o Hwf r) as HHH.
    rewrite E in HHH.
    simpl in HHH |- *.
    split; [ tauto | ].
    destruct b; firstorder.
    discriminate. intros HH.
    apply H0 in HH. discriminate.
  }
  (* i is S i *)
  assert (S i < olength os \/ S i = olength os) as [Hcase | Hcase] by lia.
  {
    (* use matcherStates_nth_error_aux2 *)
    unfold oscanMatcher.
    rewrite nth_error_map.
    destruct os as (w, o).
    pose proof (matcherStates_nth_error_aux2 w o Hwf r i Hcase) as HHH.
    destruct (nth_error (matcherStates r (w, o)) (S i)) as [[b m] | ] eqn:E;
    simpl in HHH |- *.
    2 : { rewrite nth_error_None in E. rewrite matcherStates_length in E.
     lia. auto.
    }
    split; [ tauto | ].
    destruct b; firstorder.
    discriminate. intros HH.
    apply H0 in HH. discriminate.
  }
  {
    (* use matcherStates_nth_error_aux3 *)
    unfold oscanMatcher.
    rewrite nth_error_map.
    destruct os as (w, o).
    pose proof (matcherStates_nth_error_aux3 w o Hwf r i Hcase) as HHH.
    destruct (nth_error (matcherStates r (w, o)) (S i)) as [[b m] | ] eqn:E;
    simpl in HHH |- *.
    2 : { rewrite nth_error_None in E. rewrite matcherStates_length in E.
     lia. auto.
    }
    rewrite ofirstn_all2. 2 : auto. 2 : lia.
    split; [ tauto | ].
    destruct b; firstorder.
    discriminate. intros HH.
    apply H0 in HH. discriminate.
  }
Qed.

End OMatcher.
