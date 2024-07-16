(**

The function [abstract : LRegex -> ORegex] replaces [maximal_lookarounds] of a [LRegex] with oracle queries.
- The [arity] of a [LRegex] is the number of maximal lookarounds in the [LRegex].
- The predicate [is_lookahead_tape r w t] says that the i-th value of [t] says if w[i, |w|] matches [r].
- The predicate [is_lookbehind_tape r w t] says that the i-th value of [t] says if w[0, i] matches [r].
- The predicates [is_neglookahead_tape] and [is_neglookbehind_tape] are analogous to [is_lookahead_tape] and [is_lookbehind_tape] respectively.
- We use a type [LARegex] to denote exclusively (?= r), (?<= r), (?! r), and (?<! r). 
- The function [maximal_lookarounds] returns a list of [LARegex].
- The function [is_lookaround_tape : LARegex -> list A -> list bool -> Prop] compactly represents [is_lookahead_tape], [is_lookbehind_tape], [is_neglookahead_tape], and [is_neglookbehind_tape] depending on the [LARegex].
- The predicate [oval_tapes r w ts] says that [ts] is a list of tapes (i.e, list of [bool]) such that each tape corresponds to a maximal lookaround in [r].
- The predicate [is_oval r w vs] is similar, except that it states the proposition over a sequence of valuations.
- The main lemma [oracle_compose] states that [r] can be replaced with [abstract r] if [r] is interpretted over an ostring that uses valuations that correspond to those of the maximal lookarounds.

*)

Require Import Lia.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.


Import ListNotations.

Require Import LRegex.
Require Import ORegex.
Require Import Reverse.
Require Import ListLemmas.

Section Abstraction.

Context {A : Type}.

Inductive LARegex :=
  | LALookAhead : (@LRegex A) -> LARegex
  | LALookBehind : (@LRegex A) -> LARegex
  | LANegLookAhead : (@LRegex A) -> LARegex
  | LANegLookBehind : (@LRegex A) -> LARegex
  .

Fixpoint maximal_lookarounds (r : @LRegex A) : list LARegex :=
  match r with
  | Epsilon => []
  | CharClass c => []
  | Concat r1 r2 => maximal_lookarounds r1 ++ maximal_lookarounds r2
  | Union r1 r2 => maximal_lookarounds r1 ++ maximal_lookarounds r2
  | Star r => maximal_lookarounds r
  | LookAhead r => [ LALookAhead r ]
  | LookBehind r => [ LALookBehind r ]
  | NegLookAhead r => [ LANegLookAhead r ]
  | NegLookBehind r => [ LANegLookBehind r ]
  end.

Definition arity (r : @LRegex A) : nat :=
  length (maximal_lookarounds r).

Lemma arity_eps : arity Epsilon = 0.
Proof. reflexivity. Qed.

Lemma arity_char : forall c, arity (CharClass c) = 0.
Proof. reflexivity. Qed.

Lemma arity_lookahead : forall r, arity (LookAhead r) = 1.
Proof. reflexivity. Qed.

Lemma arity_lookbehind : forall r, arity (LookBehind r) = 1.
Proof. reflexivity. Qed.

Lemma arity_neglookahead : forall r, arity (NegLookAhead r) = 1.
Proof. reflexivity. Qed.

Lemma arity_neglookbehind : forall r, arity (NegLookBehind r) = 1.
Proof. reflexivity. Qed.

Lemma arity_concat : forall r1 r2, arity (Concat r1 r2) = arity r1 + arity r2.
Proof.
  intros. unfold arity. simpl.
  rewrite app_length. auto.
Qed.

Lemma arity_union : forall r1 r2, arity (Union r1 r2) = arity r1 + arity r2.
Proof.
  intros. unfold arity. simpl.
  rewrite app_length. auto.
Qed.

Lemma arity_star : forall r, arity (Star r) = arity r.
Proof. reflexivity. Qed.

Hint Rewrite arity_eps arity_char arity_lookahead arity_lookbehind
  arity_neglookahead arity_neglookbehind arity_concat arity_union
  arity_star : regex.

Fixpoint total_arity (r : @LRegex A) : nat :=
  match r with
  | Epsilon => 0
  | CharClass c => 0
  | Concat r1 r2 => total_arity r1 + total_arity r2
  | Union r1 r2 => total_arity r1 + total_arity r2
  | Star r => total_arity r
  | LookAhead r => 1 + total_arity r
  | LookBehind r => 1 + total_arity r
  | NegLookAhead r => 1 + total_arity r
  | NegLookBehind r => 1 + total_arity r
  end.

Lemma arity_total_arity : forall r,
  arity r <= total_arity r.
Proof.
  induction r; autorewrite with regex; simpl; lia.
Qed.

Definition tape := list bool.

Fixpoint abstractAux (i : nat) (r : @LRegex A) : ORegex :=
  match r with
  | Epsilon => OEpsilon
  | CharClass c => OCharClass c
  | Concat r1 r2 => OConcat (abstractAux i r1) (abstractAux (i + arity r1) r2)
  | Union r1 r2 => OUnion (abstractAux i r1) (abstractAux (i + arity r1) r2)
  | Star r => OStar (abstractAux i r)
  | LookAhead r => OQueryPos i
  | LookBehind r => OQueryPos i
  | NegLookAhead r => OQueryNeg i
  | NegLookBehind r => OQueryNeg i
  end.

Definition abstract (r : @LRegex A) : ORegex :=
  abstractAux 0 r.

Definition is_lookbehind_tape (r : LRegex) (w : list A) (t : list bool) : Prop :=
  (length t = length w + 1) /\
    forall delta,
        delta <= length w ->
        (nth_error t delta = Some true <-> match_regex r w 0 delta) /\
        (nth_error t delta = Some false <-> ~ match_regex r w 0 delta).

Definition is_lookahead_tape (r : LRegex) (w : list A) (t : list bool) : Prop :=
  (length t = length w + 1) /\
  forall i,
      i <= length w ->
      (nth_error t i = Some true <-> match_regex r w i (length w - i)) /\
      (nth_error t i = Some false <-> ~ match_regex r w i (length w - i)).


Definition is_lookaround_tape (r : LARegex) (w : list A) (t : list bool) : Prop :=
  match r with
  | LALookAhead r1 => is_lookahead_tape r1 w t
  | LALookBehind r1 => is_lookbehind_tape r1 w t
  | LANegLookAhead r1 => is_lookahead_tape r1 w t
  | LANegLookBehind r1 => is_lookbehind_tape r1 w t
  end.

Lemma lookaround_tape_length : forall r w t,
  is_lookaround_tape r w t -> length t = length w + 1.
Proof.
  intros. destruct r; destruct H; auto.
Qed.

Lemma lookbehind_tape_is_tape : forall r w t,
  is_lookbehind_tape r w t <-> is_tape r w t.
Proof.
  unfold is_lookbehind_tape, is_tape. tauto.
Qed.

Lemma lookahead_tape_is_tape : forall r w t,
  is_lookahead_tape r w t <-> is_tape (reverse r) (rev w) (rev t).
Proof.
  intros.
  unfold is_lookahead_tape, is_tape. split.
  + intros [Hlen H].
    split. {
      now repeat rewrite rev_length.
    }
    intros i Hi.
    specialize (H (length w - i)).
    destruct H as [H1 H2]. lia.
    split.
    - rewrite nth_error_rev by now rewrite rev_length in Hi; lia. 
      replace (length t - S i) with (length w - i) by lia.
      rewrite H1. rewrite reverse_match by lia.
      rewrite rev_length in Hi.
      replace (length w - (length w - i)) with i by lia.
      replace ((length w - (length w - i + i))) with 0 by lia.
      tauto.
    - rewrite nth_error_rev. 2 : {
        now rewrite rev_length in Hi; lia.
      }
      replace (length t - S i) with (length w - i) by lia.
      rewrite H2. rewrite reverse_match by lia.
      rewrite rev_length in Hi.
      replace (length w - (length w - i)) with i by lia.
      replace ((length w - (length w - i + i))) with 0 by lia.
      tauto.
  + intros [Hlen H].
    split. {
      now repeat rewrite rev_length in Hlen.
    }
    intros i Hi.
    specialize (H (length w - i)).
    destruct H as [H1 H2]. rewrite rev_length. lia.
    split.
    - rewrite reverse_match by lia.
      replace (length w - (i + (length w - i))) with 0 by lia.
      rewrite <- H1.
      repeat rewrite rev_length in Hlen.
      replace i with (length t - (length t - i)) at 1 by lia. 
      rewrite nth_error_rev. 
      replace (S (length w - i)) with (length t - i) by lia.
      tauto. lia.
    - rewrite reverse_match by lia.
      replace (length w - (i + (length w - i))) with 0 by lia.
      rewrite <- H2.
      repeat rewrite rev_length in Hlen.
      replace i with (length t - (length t - i)) at 1 by lia. 
      rewrite nth_error_rev. 
      replace (S (length w - i)) with (length t - i) by lia.
      tauto. lia. 
Qed.

Definition oval_tapes_aux (e : @LRegex A) (w : list A) (s : nat) (ts : list tape) : Prop :=
  length ts >= s + arity e
  /\ (forall t, In t ts -> length t = length w + 1)
  /\ forall i t r,
    i < arity e
    -> nth_error ts (s + i) = Some t
    -> nth_error (maximal_lookarounds e) i = Some r
    -> is_lookaround_tape r w t.

Lemma oval_tapes_aux_firstn (e : @LRegex A) (w : list A) (s : nat) (ts : list tape) :
  oval_tapes_aux e w s ts
  -> oval_tapes_aux e w s (firstn (s + arity e) ts).
Proof.
  intros [Hlen [Hlen' H]].
  split. {
    rewrite firstn_length_le. auto.
    lia.
  }
  split. {
    intros t Ht. apply firstn_In in Ht.
    auto.
  }
  intros i t r Hi Hnth Hnth'.
  apply H with (i := i). auto.
  rewrite nth_error_firstn in Hnth. auto.
  lia. auto.
Qed.

Lemma oval_tapes_aux_skipn (e : @LRegex A) (w : list A) (𝛼 d : nat) (ts : list tape) :
  d <= 𝛼
  -> oval_tapes_aux e w 𝛼 ts
  -> oval_tapes_aux e w (𝛼 - d) (skipn d ts).
Proof.
  intros Hd [Hlen [Hlen' H]].
  split. {
    rewrite skipn_length. lia.
  }
  split. {
    intros t Ht. apply skipn_In in Ht.
    auto.
  }
  intros i t r Hi Hnth Hnth'.
  apply H with (i := i). auto.
  rewrite <- nth_error_skipn in Hnth.
  replace (𝛼 - d + i + d) with (𝛼 + i ) in Hnth by lia. auto.
  auto.
Qed.


Lemma oval_tapes_eps : forall w 𝛼 ts,
  oval_tapes_aux Epsilon w 𝛼 ts
  <-> length ts >= 𝛼
    /\ (forall t, In t ts -> length t = length w + 1).
Proof.
  intros. unfold oval_tapes_aux.
  unfold arity. simpl. 
  replace (𝛼 + 0) with 𝛼 by lia. split.
  - intros [Hlen [Hlen' _]]. auto.
  - intros [Hlen Hlen']. repeat split; auto.
    intros. lia.
Qed.

Lemma oval_tapes_charclass : forall c w 𝛼 ts,
  oval_tapes_aux (CharClass c) w 𝛼 ts
  <-> length ts >= 𝛼
    /\ (forall t, In t ts -> length t = length w + 1).
Proof.
  intros. unfold oval_tapes_aux.
  unfold arity. simpl. 
  replace (𝛼 + 0) with 𝛼 by lia. split.
  - intros [Hlen [Hlen' _]]. auto.
  - intros [Hlen Hlen']. repeat split; auto.
    intros. lia.
Qed.


Lemma oval_tapes_concat : forall e1 e2 w 𝛼 ts,
  oval_tapes_aux (Concat e1 e2) w 𝛼 ts
  <-> (oval_tapes_aux e1 w 𝛼 ts
      /\ oval_tapes_aux e2 w (𝛼 + arity e1) ts).
Proof.
  intros. split.
  - intros [Hlen [Hlen' Htapes]].
    rewrite arity_concat in Hlen. split.
    + split.
      lia. split.
      auto.
      intros. apply Htapes with (i := i). 
      rewrite arity_concat. lia. auto.
      simpl maximal_lookarounds. 
      rewrite nth_error_app1. auto. unfold arity in H. auto.
    + split. 
      lia. split.
      auto.
      intros. apply Htapes with (i := arity e1 + i).
      rewrite arity_concat. lia.
      replace (𝛼 + (arity e1 + i)) with (𝛼 + arity e1 + i) by lia. auto.
      simpl maximal_lookarounds.
      rewrite nth_error_app2. unfold arity.
      replace (length (maximal_lookarounds e1) + i - length (maximal_lookarounds e1)) with i by lia.
      auto. unfold arity. lia.
  - intros [[Hlen1 [Hlen1' Htapes1]] [Hlen2 [Hlen2' Htapes2]]].
    split. rewrite arity_concat. lia.
    split. auto.
    intros. rewrite arity_concat in H.
    simpl maximal_lookarounds in H1.
    assert (i < arity e1 \/ (arity e1 <= i)) as Hi by lia.
    destruct Hi as [Hi | Hi].
    + apply Htapes1 with (i := i). auto.
      auto.
      replace (𝛼 + i) with (𝛼 + 0 + i) by lia. auto.
      rewrite nth_error_app1 in H1. auto. unfold arity in Hi. auto.
    + apply Htapes2 with (i := i - arity e1). lia.
      replace (𝛼 + arity e1 + (i - arity e1)) with (𝛼 + i) by lia. auto.
      rewrite nth_error_app2 in H1. auto. unfold arity in Hi. lia.
Qed.

Lemma oval_tapes_union : forall e1 e2 w 𝛼 ts,
  oval_tapes_aux (Union e1 e2) w 𝛼 ts
  <-> (oval_tapes_aux e1 w 𝛼 ts
    /\ oval_tapes_aux e2 w (𝛼 + arity e1) ts).
Proof.
  intros. split.
  - intros [Hlen [Hlen' Htapes]].
    rewrite arity_union in Hlen. split.
    + split.
      lia. split.
      auto.
      intros. apply Htapes with (i := i). 
      rewrite arity_union. lia. auto.
      simpl maximal_lookarounds. 
      rewrite nth_error_app1. auto. unfold arity in H. auto.
    + split. 
      lia. split.
      auto.
      intros. apply Htapes with (i := arity e1 + i).
      rewrite arity_union. lia.
      replace (𝛼 + (arity e1 + i)) with (𝛼 + arity e1 + i) by lia. auto.
      simpl maximal_lookarounds.
      rewrite nth_error_app2. unfold arity.
      replace (length (maximal_lookarounds e1) + i - length (maximal_lookarounds e1)) with i by lia.
      auto. unfold arity. lia.
  - intros [[Hlen1 [Hlen1' Htapes1]] [Hlen2 [Hlen2' Htapes2]]].
    split. rewrite arity_union. lia.
    split. auto.
    intros. rewrite arity_union in H.
    simpl maximal_lookarounds in H1.
    assert (i < arity e1 \/ (arity e1 <= i)) as Hi by lia.
    destruct Hi as [Hi | Hi].
    + apply Htapes1 with (i := i). auto.
      auto.
      replace (𝛼 + i) with (𝛼 + 0 + i) by lia. auto.
      rewrite nth_error_app1 in H1. auto. unfold arity in Hi. auto.
    + apply Htapes2 with (i := i - arity e1). lia.
      replace (𝛼 + arity e1 + (i - arity e1)) with (𝛼 + i) by lia. auto.
      rewrite nth_error_app2 in H1. auto. unfold arity in Hi. lia.
Qed.

Lemma oval_tapes_star : forall e w 𝛼 ts,
  oval_tapes_aux (Star e) w 𝛼 ts
  <-> oval_tapes_aux e w 𝛼 ts.
Proof.
  intros. split; intros H; destruct H as [H0 [H1 H2]].
  - rewrite arity_star in H0. firstorder.
  - split. 
    rewrite arity_star. auto.
    split; auto.
Qed.

Lemma oval_tapes_lookahead : forall e w 𝛼 ts,
  oval_tapes_aux (LookAhead e) w 𝛼 ts
  <-> length ts >= 𝛼 + 1
  /\ (forall t, In t ts -> length t = length w + 1)
  /\ exists t,
    nth_error ts 𝛼 = Some t
    /\ is_lookahead_tape e w t.
Proof.
  intros. split; intros H; destruct H as [H0 [H1 H2]].
  - rewrite arity_lookahead in H0. split; [auto | ].
    split; [auto | ].
    destruct (nth_error ts 𝛼) eqn:Et. 2 : {
      rewrite nth_error_None in Et. lia.
    }     
    exists t. split; auto.
    specialize (H2 0 t (LALookAhead e)). unfold arity in H2.
    simpl in H2. replace (𝛼 + 0) with 𝛼 in H2 by lia.
    specialize (H2 ltac:(lia) Et eq_refl). auto.
  - destruct H2 as [t [Ht1 Ht2]].
    split. rewrite arity_lookahead. auto.
    split. auto.
    intros. simpl maximal_lookarounds in H3.
    rewrite arity_lookahead in H.
    assert (i = 0) by lia. subst i.
    simpl in H3. inversion H3. simpl.
    replace (𝛼 + 0) with 𝛼 in H2 by lia.
    congruence.
Qed.

Lemma oval_tapes_lookbehind : forall e w 𝛼 ts,
  oval_tapes_aux (LookBehind e) w 𝛼 ts
  <-> length ts >= 𝛼 + 1
  /\ (forall t, In t ts -> length t = length w + 1)
  /\ exists t,
    nth_error ts 𝛼 = Some t
    /\ is_lookbehind_tape e w t.
Proof.
  intros. split; intros H; destruct H as [H0 [H1 H2]].
  - rewrite arity_lookbehind in H0. split; [auto | ].
    split; [auto | ].
    destruct (nth_error ts 𝛼) eqn:Et. 2 : {
      rewrite nth_error_None in Et. lia.
    }     
    exists t. split; auto.
    specialize (H2 0 t (LALookBehind e)). unfold arity in H2.
    simpl in H2. replace (𝛼 + 0) with 𝛼 in H2 by lia.
    specialize (H2 ltac:(lia) Et eq_refl). auto.
  - destruct H2 as [t [Ht1 Ht2]].
    split. rewrite arity_lookbehind. auto.
    split. auto.
    intros. simpl maximal_lookarounds in H3.
    rewrite arity_lookbehind in H.
    assert (i = 0) by lia. subst i.
    simpl in H3. inversion H3. simpl.
    replace (𝛼 + 0) with 𝛼 in H2 by lia.
    congruence.
Qed.

Lemma oval_tapes_neglookahead : forall e w 𝛼 ts,
  oval_tapes_aux (NegLookAhead e) w 𝛼 ts
  <-> length ts >= 𝛼 + 1
  /\ (forall t, In t ts -> length t = length w + 1)
  /\ exists t,
    nth_error ts 𝛼 = Some t
    /\ is_lookahead_tape e w t.
Proof.
  intros. split; intros H; destruct H as [H0 [H1 H2]].
  - rewrite arity_neglookahead in H0. split; [auto | ].
    split; [auto | ].
    destruct (nth_error ts 𝛼) eqn:Et. 2 : {
      rewrite nth_error_None in Et. lia.
    }     
    exists t. split; auto.
    specialize (H2 0 t (LANegLookAhead e)). unfold arity in H2.
    simpl in H2. replace (𝛼 + 0) with 𝛼 in H2 by lia.
    specialize (H2 ltac:(lia) Et eq_refl). auto.
  - destruct H2 as [t [Ht1 Ht2]].
    split. rewrite arity_neglookahead. auto.
    split. auto.
    intros. simpl maximal_lookarounds in H3.
    rewrite arity_neglookahead in H.
    assert (i = 0) by lia. subst i.
    simpl in H3. inversion H3. simpl.
    replace (𝛼 + 0) with 𝛼 in H2 by lia.
    congruence.
Qed.

Lemma oval_tapes_neglookbehind : forall e w 𝛼 ts,
  oval_tapes_aux (NegLookBehind e) w 𝛼 ts
  <-> length ts >= 𝛼 + 1
  /\ (forall t, In t ts -> length t = length w + 1)
  /\ exists t,
    nth_error ts 𝛼 = Some t
    /\ is_lookbehind_tape e w t.
Proof.
  intros. split; intros H; destruct H as [H0 [H1 H2]].
  - rewrite arity_neglookbehind in H0. split; [auto | ].
    split; [auto | ].
    destruct (nth_error ts 𝛼) eqn:Et. 2 : {
      rewrite nth_error_None in Et. lia.
    }     
    exists t. split; auto.
    specialize (H2 0 t (LANegLookBehind e)). unfold arity in H2.
    simpl in H2. replace (𝛼 + 0) with 𝛼 in H2 by lia.
    specialize (H2 ltac:(lia) Et eq_refl). auto.
  - destruct H2 as [t [Ht1 Ht2]].
    split. rewrite arity_neglookbehind. auto.
    split. auto.
    intros. simpl maximal_lookarounds in H3.
    rewrite arity_neglookbehind in H.
    assert (i = 0) by lia. subst i.
    simpl in H3. inversion H3. simpl.
    replace (𝛼 + 0) with 𝛼 in H2 by lia.
    congruence.
Qed.

   
Definition oval_tapes (e : @LRegex A) (w : list A) (ts : list tape) : Prop :=
    oval_tapes_aux e w 0 ts.

Definition is_oval_aux (r : @LRegex A) (w : list A) (s : nat) (vs : list valuation) : Prop :=
  exists ts, oval_tapes_aux r w s ts /\ vs = transpose (length w + 1) ts.

Definition is_oval (r : @LRegex A) (w : list A) (vs : list valuation) : Prop :=
  is_oval_aux r w 0 vs.

Lemma wf_oval (r : @LRegex A) (w : list A) (vs : list valuation) :
  forall s, 
  is_oval_aux r w s vs
  -> ostring_wf (w, vs).
Proof.
  intros s [ts [Hts Hvs]].
  unfold ostring_wf. split.
  - unfold outer_length_wf.
    simpl. rewrite Hvs.
    rewrite (@transpose_length bool).
    + auto.
    + intros t Ht. apply Hts in Ht.
      lia.
  - unfold inner_length_wf.
    simpl. intros i j Hi Hj. 
    subst. apply transpose_inner_length in Hj, Hi.
    congruence.
Qed.

Lemma oracle_compose_aux (r : @LRegex A) (w : list A) (𝛼 : nat) (vs : list valuation) :
  is_oval_aux r w 𝛼 vs
  -> forall start delta,
       start + delta <= length w
    -> match_regex r w start delta
    <-> match_oregex (abstractAux 𝛼 r) (ofirstn delta (oskipn start (w, vs))).
Proof.
  revert 𝛼 w vs. induction r.
  - intros. rewrite match_eps_iff.
    simpl. destruct H as [ts [Hts Hvs]].
    rewrite oval_tapes_eps in Hts.
    destruct Hts as [Hlen1 Hlen2].
    split; intros H.
    + subst.
      apply omatch_epsilon.
      rewrite ofirstn_olength. auto.
    + inversion H. subst.
      rewrite ofirstn_olength in H1.
      rewrite oskipn_olength in H1.
      unfold olength in H1. simpl in H1.
      lia.
  - intros. rewrite match_class_iff.
    simpl. destruct H as [ts [Hts Hvs]].
    rewrite oval_tapes_charclass in Hts.
    destruct Hts as [Hlen1 Hlen2].
    split; intros H.
    + destruct H as [a [Ha1 [Ha2 Hd]]].
      apply omatch_charclass with (a := a); auto.
      rewrite ofirstn_olength. rewrite oskipn_olength.
      unfold olength. simpl. lia. {
        unfold oskipn. simpl.
        rewrite hd_error_nth_error.
        replace delta with (start + delta - start) by lia.
        rewrite <- skipn_firstn_comm.
        rewrite <- hd_error_nth_error.
        rewrite hd_error_skipn.
        rewrite <- firstn_skipn with (l := w) (n := start + delta) in Ha2.
        rewrite nth_error_app1 in Ha2. auto.
        rewrite firstn_length. lia.
      }
    + inversion H. subst.
      exists a. split; auto.
      rewrite ofirstn_olength in H2.
      rewrite oskipn_olength in H2.
      unfold olength in H2. simpl in H2.
      simpl in H3.
      replace delta with (start + delta - start) in H3 by lia.
      rewrite <- skipn_firstn_comm in H3.
      rewrite hd_error_skipn in H3.
      rewrite <- firstn_skipn with (l := w) (n := start + delta).
      split.
      * rewrite nth_error_app1. auto.
        rewrite firstn_length. lia.
      * lia.  
  - intros. simpl. rewrite match_concat_iff.
    split. {
      intros [d1 [d2 [Hr1 [Hr2 Hd]]]].
      unfold is_oval_aux in H.
      destruct H as [ts [Hts Hvs]].
      rewrite oval_tapes_concat in Hts.
      destruct Hts as [Hts1 Hts2].
      apply omatch_concat with (n := d1).
      + rewrite ofirstn_ofirstn.
        replace (min d1 delta) with d1 by lia.
        rewrite <- IHr1; auto.
        exists ts. split; auto.
        lia. 
      + rewrite oskipn_ofirstn_comm.
        rewrite oskipn_oskipn.
        rewrite <- IHr2.
        replace (d1 + start) with (start + d1) by lia.
        replace (delta - d1) with d2 by lia.
        auto.
        exists ts. split; auto.
        lia.
        apply oskipn_outer_length_wf.
        unfold outer_length_wf. simpl.
        rewrite Hvs.
        rewrite (@transpose_length bool); auto.
        unfold oval_tapes_aux in Hts2.
        destruct Hts2 as [Hts [Ht _]].
        intros. enough (length t = length w + 1) by lia.
        auto. lia.
    } {
      intros Hor12.
      unfold is_oval_aux in H.
      destruct H as [ts [Hts Hvs]].
      rewrite oval_tapes_concat in Hts.
      destruct Hts as [Hts1 Hts2].
      rewrite omatch_concat_iff in Hor12.
      destruct Hor12 as [d [ Hd [Hr1 Hr2]]].
      rewrite ofirstn_olength in Hd.
      rewrite oskipn_olength in Hd.
      unfold olength in Hd. simpl in Hd.
      replace (min delta (length w - start)) with delta in Hd by lia.
      rewrite ofirstn_ofirstn in Hr1.
      replace (min d delta) with d in Hr1 by lia.
      rewrite oskipn_ofirstn_comm in Hr2.
      rewrite oskipn_oskipn in Hr2.
      exists d, (delta - d). repeat split.
      + rewrite IHr1. apply Hr1.
        exists ts. split; eauto.
        lia.
      + rewrite IHr2.
        replace (start + d) with (d + start) by lia. apply Hr2.
        exists ts. split; eauto.
        lia.
      + lia.
      + apply oskipn_outer_length_wf.
        unfold outer_length_wf. simpl.
        rewrite Hvs.
        rewrite (@transpose_length bool); auto.
        unfold oval_tapes_aux in Hts2.
        destruct Hts2 as [Hts [Ht _]].
        intros. enough (length t = length w + 1) by lia.
        auto.
      + lia.
      + apply ofirstn_outer_length_wf.
        apply oskipn_outer_length_wf.
        unfold outer_length_wf. simpl.
        rewrite Hvs.
        rewrite (@transpose_length bool); auto.
        unfold oval_tapes_aux in Hts2.
        destruct Hts2 as [Hts [Ht _]].
        intros. enough (length t = length w + 1) by lia.
        auto. 
    }
  - intros. simpl. rewrite match_union_iff.
    split. {
      intros.
      destruct H1.
      + rewrite IHr1 in H1.
      apply omatch_union_l.
      apply H1.
      unfold is_oval_aux in H.
      destruct H as [ts [Hts Hvs]].
      rewrite oval_tapes_union in Hts.
      destruct Hts as [Hts1 Hts2].
      exists ts. split; auto.
      lia.
      + apply omatch_union_r.
      rewrite <- IHr2.
      apply H1.
      unfold is_oval_aux in H.
      destruct H as [ts [Hts Hvs]].
      rewrite oval_tapes_union in Hts.
      destruct Hts as [Hts1 Hts2].
      exists ts. split; auto.
      lia.
    } {
    intros.
    inversion H1; subst.
    + left. rewrite IHr1.
      apply H5.
      unfold is_oval_aux in H.
      destruct H as [ts [Hts Hvs]].
      rewrite oval_tapes_union in Hts.
      destruct Hts as [Hts1 Hts2].
      exists ts. split; auto.
      lia.
    + right. rewrite IHr2.
      apply H5.
      unfold is_oval_aux in H.
      destruct H as [ts [Hts Hvs]].
      rewrite oval_tapes_union in Hts.
      destruct Hts as [Hts1 Hts2].
      exists ts. split; auto.
      lia.    
    }
  - intros. revert H0. revert start.
    unfold is_oval_aux in H.
    destruct H as [ts [Hts Hvs]].
    rewrite oval_tapes_star in Hts.
    induction delta using lt_wf_ind.
    intros start Hw.
    simpl. rewrite match_star_nonempty.
    rewrite omatch_star_nonempty.
    2 : {
      apply ofirstn_outer_length_wf.
      apply oskipn_outer_length_wf.
      unfold outer_length_wf. simpl.
      rewrite Hvs.
      rewrite (@transpose_length bool); auto.
      unfold oval_tapes_aux in Hts.
      destruct Hts as [Hts [Ht _]].
      intros. enough (length t = length w + 1) by lia.
      auto.
    }
    split. {
      intros [d | [d [Hd1 [Hd2 [Hr Hr']]]]]. {
        subst delta. left.
        rewrite ofirstn_olength.
        auto.
      }
      right. exists d. repeat split; auto.
      + rewrite ofirstn_olength.
        rewrite oskipn_olength.
        unfold olength. simpl. lia.
      + rewrite ofirstn_ofirstn.
        replace (min d delta) with d by lia.
        rewrite <- IHr. auto.
        exists ts; auto.
        lia.
      + simpl in H.
        rewrite oskipn_ofirstn_comm.
        rewrite oskipn_oskipn.
        rewrite <- H.
        replace (d + start) with (start + d) by lia.
        auto.
        lia. lia. {
          apply oskipn_outer_length_wf.
          unfold outer_length_wf. simpl.
          rewrite Hvs.
          rewrite (@transpose_length bool); auto.
          unfold oval_tapes_aux in Hts.
          destruct Hts as [Hts [Ht _]].
          intros. enough (length t = length w + 1) by lia.
          auto.
        }
        lia.
    } {
      intros [Hd | [d [Hd1 [Hd2 [Hr Hr']]]]]. {
        rewrite ofirstn_olength in Hd.
        rewrite oskipn_olength in Hd.
        unfold olength in Hd. simpl in Hd.
        replace (min delta (length w - start)) with delta in Hd by lia.
        auto.
      }
      right. 
      rewrite ofirstn_olength in Hd2.
      rewrite oskipn_olength in Hd2.
      unfold olength in Hd2. simpl in Hd2.
      replace (min delta (length w - start)) with delta in Hd2 by lia.
      rewrite ofirstn_ofirstn in Hr.
      replace (min d delta) with d in Hr by lia.
      rewrite oskipn_ofirstn_comm in Hr'.
      rewrite oskipn_oskipn in Hr'.
      rewrite <-IHr in Hr.
      rewrite <- H in Hr'.
      exists d. repeat split; auto.
      replace (d + start) with (start + d) in Hr' by lia. auto.
      lia. lia.
      exists ts; auto.
      lia. {
        apply oskipn_outer_length_wf.
        unfold outer_length_wf. simpl.
        rewrite Hvs.
        rewrite (@transpose_length bool); auto.
        unfold oval_tapes_aux in Hts.
        destruct Hts as [Hts [Ht _]].
        intros. enough (length t = length w + 1) by lia.
        auto.
      }
      auto.
    } 
  - intros.
    unfold is_oval_aux in H.
    destruct H as [ts [Hts Hvs]].
    unfold oval_tapes_aux in Hts.
    destruct Hts as [Hts [Ht Hs]].
    simpl in *. rewrite arity_lookahead in Hts.
    rewrite arity_lookahead in Hs.
    assert (𝛼 < length ts) by lia.
    rewrite <- nth_error_Some in H.
    destruct (nth_error ts 𝛼) as [t | ] eqn:Ht'; [ | congruence].
    clear H.
    specialize (Hs 0 t (LALookAhead r) ltac:(lia)).
    replace (𝛼 + 0) with 𝛼 in Hs by lia. simpl in Hs.
    specialize (Hs Ht' eq_refl).
    rewrite match_lookahead_iff. split.
    + intros [Hr Hd].
      subst. unfold ofirstn. simpl fst. simpl snd.
      simpl firstn at 1.
      replace (min start (length w)) with start by lia.
      remember  (firstn 1 (skipn start (transpose (length w + 1) ts))) as l.
      assert (0 < length l). {
        subst l. rewrite firstn_length.
        rewrite skipn_length.
        rewrite min_l; auto.
        rewrite (@transpose_length bool); auto.
        lia. intros.
        enough (length t0 = length w + 1) by lia.
        auto.
      }
      rewrite <- nth_error_Some in H.
      destruct (nth_error l 0) as [v | ] eqn:Hv; [ | congruence].
      apply omatch_query_pos with (v := v).
      * unfold olength. simpl. auto.
      * remember 1 as one. simpl.
        subst. rewrite hd_error_nth_error.
        auto.
      * subst.
        unfold is_lookahead_tape in Hs.
        destruct Hs as [Hs1 Hs2].
        specialize (Hs2 start ltac:(lia)).
        destruct Hs2 as [Hs2  Hs3].
        rewrite <- Hs2 in Hr.
        rewrite nth_error_firstn in Hv by lia.
        rewrite <- nth_error_skipn in Hv. simpl in Hv.
        assert (@ij_error bool 𝛼 start ts = Some true). {
          unfold ij_error.
          unfold tape in Ht'. rewrite Ht'. auto.
        }
        rewrite transpose_spec with (len := length w + 1) in H1 by auto.
        unfold ij_error in H1. rewrite Hv in H1. auto.
    + intros Homatch. inversion Homatch.
      subst q.
      rewrite ofirstn_olength in H1.
      rewrite oskipn_olength in H1.
      unfold olength in H1. simpl in H1.
      assert (delta = 0) as Hdelta by lia.
      split; auto. subst delta.
      remember (oskipn start (w, vs)) as os'.
      destruct os' as [w' vs'].
      unfold ofirstn in *. simpl fst in *.
      rewrite firstn_O in H4. remember 1 as one.
      simpl snd in *. subst one.
      unfold oskipn in Heqos'. simpl in Heqos'.
      replace (min start (length w)) with start in Heqos' by lia.
      inversion Heqos'. clear Heqos'. clear Homatch.
      unfold is_lookahead_tape in Hs.
      destruct Hs as [Hs1 Hs2].
      specialize (Hs2 start ltac:(lia)).
      destruct Hs2 as [Hs2  Hs3].
      rewrite <- Hs2.
      subst vs'.
      rewrite hd_error_nth_error in H2.
      rewrite nth_error_firstn in H2 by lia.
      rewrite <- nth_error_skipn in H2. simpl in H2.
      assert (@ij_error bool 𝛼 start ts = Some true). {
        rewrite transpose_spec with (len := length w + 1) by auto.
        unfold ij_error.
        rewrite <- Hvs.
        unfold valuation in H2. rewrite H2. auto.
      }
      unfold ij_error in H. unfold tape in Ht'. rewrite Ht' in H. auto.
  - intros.
    unfold is_oval_aux in H.
    destruct H as [ts [Hts Hvs]].
    unfold oval_tapes_aux in Hts.
    destruct Hts as [Hts [Ht Hs]].
    simpl in *. rewrite arity_lookbehind in Hts.
    rewrite arity_lookbehind in Hs.
    assert (𝛼 < length ts) by lia.
    rewrite <- nth_error_Some in H.
    destruct (nth_error ts 𝛼) as [t | ] eqn:Ht'; [ | congruence].
    clear H.
    specialize (Hs 0 t (LALookBehind r) ltac:(lia)).
    replace (𝛼 + 0) with 𝛼 in Hs by lia. simpl in Hs.
    specialize (Hs Ht' eq_refl).
    rewrite match_lookbehind_iff. split.
    + intros [Hr Hd].
      subst. unfold ofirstn. simpl fst. simpl snd.
      simpl firstn at 1.
      replace (min start (length w)) with start by lia.
      remember  (firstn 1 (skipn start (transpose (length w + 1) ts))) as l.
      assert (0 < length l). {
        subst l. rewrite firstn_length.
        rewrite skipn_length.
        rewrite min_l; auto.
        rewrite (@transpose_length bool); auto.
        lia. intros.
        enough (length t0 = length w + 1) by lia.
        auto.
      }
      rewrite <- nth_error_Some in H.
      destruct (nth_error l 0) as [v | ] eqn:Hv; [ | congruence].
      apply omatch_query_pos with (v := v).
      * unfold olength. simpl. auto.
      * remember 1 as one. simpl.
        subst. rewrite hd_error_nth_error.
        auto.
      * subst.
        unfold is_lookbehind_tape in Hs.
        destruct Hs as [Hs1 Hs2].
        specialize (Hs2 start ltac:(lia)).
        destruct Hs2 as [Hs2  Hs3].
        rewrite <- Hs2 in Hr.
        rewrite nth_error_firstn in Hv by lia.
        rewrite <- nth_error_skipn in Hv. simpl in Hv.
        assert (@ij_error bool 𝛼 start ts = Some true). {
          unfold ij_error.
          unfold tape in Ht'. rewrite Ht'. auto.
        }
        rewrite transpose_spec with (len := length w + 1) in H1 by auto.
        unfold ij_error in H1. rewrite Hv in H1. auto.
    + intros Homatch. inversion Homatch.
      subst q.
      rewrite ofirstn_olength in H1.
      rewrite oskipn_olength in H1.
      unfold olength in H1. simpl in H1.
      assert (delta = 0) as Hdelta by lia.
      split; auto. subst delta.
      remember (oskipn start (w, vs)) as os'.
      destruct os' as [w' vs'].
      unfold ofirstn in *. simpl fst in *.
      rewrite firstn_O in H4. remember 1 as one.
      simpl snd in *. subst one.
      unfold oskipn in Heqos'. simpl in Heqos'.
      replace (min start (length w)) with start in Heqos' by lia.
      inversion Heqos'. clear Heqos'. clear Homatch.
      unfold is_lookbehind_tape in Hs.
      destruct Hs as [Hs1 Hs2].
      specialize (Hs2 start ltac:(lia)).
      destruct Hs2 as [Hs2  Hs3].
      rewrite <- Hs2.
      subst vs'.
      rewrite hd_error_nth_error in H2.
      rewrite nth_error_firstn in H2 by lia.
      rewrite <- nth_error_skipn in H2. simpl in H2.
      assert (@ij_error bool 𝛼 start ts = Some true). {
        rewrite transpose_spec with (len := length w + 1) by auto.
        unfold ij_error.
        rewrite <- Hvs.
        unfold valuation in H2. rewrite H2. auto.
      }
      unfold ij_error in H. unfold tape in Ht'. rewrite Ht' in H. auto. 
  - intros.
    unfold is_oval_aux in H.
    destruct H as [ts [Hts Hvs]].
    unfold oval_tapes_aux in Hts.
    destruct Hts as [Hts [Ht Hs]].
    simpl in *. rewrite arity_neglookahead in Hts.
    rewrite arity_neglookahead in Hs.
    assert (𝛼 < length ts) by lia.
    rewrite <- nth_error_Some in H.
    destruct (nth_error ts 𝛼) as [t | ] eqn:Ht'; [ | congruence].
    clear H.
    specialize (Hs 0 t (LANegLookAhead r) ltac:(lia)).
    replace (𝛼 + 0) with 𝛼 in Hs by lia. simpl in Hs.
    specialize (Hs Ht' eq_refl).
    rewrite match_neglookahead_iff. split.
    + intros [Hr Hd].
      subst. unfold ofirstn. simpl fst. simpl snd.
      simpl firstn at 1.
      replace (min start (length w)) with start by lia.
      remember  (firstn 1 (skipn start (transpose (length w + 1) ts))) as l.
      assert (0 < length l). {
        subst l. rewrite firstn_length.
        rewrite skipn_length.
        rewrite min_l; auto.
        rewrite (@transpose_length bool); auto.
        lia. intros.
        enough (length t0 = length w + 1) by lia.
        auto.
      }
      rewrite <- nth_error_Some in H.
      destruct (nth_error l 0) as [v | ] eqn:Hv; [ | congruence].
      apply omatch_query_neg with (v := v).
      * unfold olength. simpl. auto.
      * remember 1 as one. simpl.
        subst. rewrite hd_error_nth_error.
        auto.
      * subst.
        unfold is_lookahead_tape in Hs.
        destruct Hs as [Hs1 Hs2].
        specialize (Hs2 start ltac:(lia)).
        destruct Hs2 as [Hs2  Hs3].
        rewrite <- match_not_match in Hr.
        rewrite <- Hs2 in Hr.
        rewrite nth_error_firstn in Hv by lia.
        rewrite <- nth_error_skipn in Hv. simpl in Hv.
        assert (@ij_error bool 𝛼 start ts = Some false). {
          unfold ij_error.
          unfold tape in Ht'. rewrite Ht'.
          pose proof match_lem r w start (length w - start) as [Hlem1 | Hlem2].
          - rewrite <- Hs2 in Hlem1. contradiction.
          - rewrite <- Hs3 in Hlem2. auto. 
        }
        rewrite transpose_spec with (len := length w + 1) in H1 by auto.
        unfold ij_error in H1. rewrite Hv in H1. auto.
    + intros Homatch. inversion Homatch.
      subst q.
      rewrite ofirstn_olength in H1.
      rewrite oskipn_olength in H1.
      unfold olength in H1. simpl in H1.
      assert (delta = 0) as Hdelta by lia.
      split; auto. subst delta.
      remember (oskipn start (w, vs)) as os'.
      destruct os' as [w' vs'].
      unfold ofirstn in *. simpl fst in *.
      rewrite firstn_O in H4. remember 1 as one.
      simpl snd in *. subst one.
      unfold oskipn in Heqos'. simpl in Heqos'.
      replace (min start (length w)) with start in Heqos' by lia.
      inversion Heqos'. clear Heqos'. clear Homatch.
      unfold is_lookahead_tape in Hs.
      destruct Hs as [Hs1 Hs2].
      specialize (Hs2 start ltac:(lia)).
      destruct Hs2 as [Hs2  Hs3].
      rewrite <- match_not_match.
      rewrite <- Hs2.
      subst vs'.
      rewrite hd_error_nth_error in H2.
      rewrite nth_error_firstn in H2 by lia.
      rewrite <- nth_error_skipn in H2. simpl in H2.
      assert (@ij_error bool 𝛼 start ts = Some false). {
        rewrite transpose_spec with (len := length w + 1) by auto.
        unfold ij_error.
        rewrite <- Hvs.
        unfold valuation in H2. rewrite H2. auto.
      }
      unfold ij_error in H. unfold tape in Ht'. rewrite Ht' in H.
      rewrite H. discriminate.
  - intros.
    unfold is_oval_aux in H.
    destruct H as [ts [Hts Hvs]].
    unfold oval_tapes_aux in Hts.
    destruct Hts as [Hts [Ht Hs]].
    simpl in *. rewrite arity_neglookbehind in Hts.
    rewrite arity_neglookbehind in Hs.
    assert (𝛼 < length ts) by lia.
    rewrite <- nth_error_Some in H.
    destruct (nth_error ts 𝛼) as [t | ] eqn:Ht'; [ | congruence].
    clear H.
    specialize (Hs 0 t (LANegLookBehind r) ltac:(lia)).
    replace (𝛼 + 0) with 𝛼 in Hs by lia. simpl in Hs.
    specialize (Hs Ht' eq_refl).
    rewrite match_neglookbehind_iff. split.
    + intros [Hr Hd].
      subst. unfold ofirstn. simpl fst. simpl snd.
      simpl firstn at 1.
      replace (min start (length w)) with start by lia.
      remember  (firstn 1 (skipn start (transpose (length w + 1) ts))) as l.
      assert (0 < length l). {
        subst l. rewrite firstn_length.
        rewrite skipn_length.
        rewrite min_l; auto.
        rewrite (@transpose_length bool); auto.
        lia. intros.
        enough (length t0 = length w + 1) by lia.
        auto.
      }
      rewrite <- nth_error_Some in H.
      destruct (nth_error l 0) as [v | ] eqn:Hv; [ | congruence].
      apply omatch_query_neg with (v := v).
      * unfold olength. simpl. auto.
      * remember 1 as one. simpl.
        subst. rewrite hd_error_nth_error.
        auto.
      * subst.
        unfold is_lookbehind_tape in Hs.
        destruct Hs as [Hs1 Hs2].
        specialize (Hs2 start ltac:(lia)).
        destruct Hs2 as [Hs2  Hs3].
        rewrite <- match_not_match in Hr.
        rewrite <- Hs2 in Hr.
        rewrite nth_error_firstn in Hv by lia.
        rewrite <- nth_error_skipn in Hv. simpl in Hv.
        assert (@ij_error bool 𝛼 start ts = Some false). {
          unfold ij_error.
          unfold tape in Ht'. rewrite Ht'.
          pose proof match_lem r w 0 start as [Hlem1 | Hlem2].
          - rewrite <- Hs2 in Hlem1. contradiction.
          - rewrite <- Hs3 in Hlem2. auto. 
        }
        rewrite transpose_spec with (len := length w + 1) in H1 by auto.
        unfold ij_error in H1. rewrite Hv in H1. auto.
    + intros Homatch. inversion Homatch.
      subst q.
      rewrite ofirstn_olength in H1.
      rewrite oskipn_olength in H1.
      unfold olength in H1. simpl in H1.
      assert (delta = 0) as Hdelta by lia.
      split; auto. subst delta.
      remember (oskipn start (w, vs)) as os'.
      destruct os' as [w' vs'].
      unfold ofirstn in *. simpl fst in *.
      rewrite firstn_O in H4. remember 1 as one.
      simpl snd in *. subst one.
      unfold oskipn in Heqos'. simpl in Heqos'.
      replace (min start (length w)) with start in Heqos' by lia.
      inversion Heqos'. clear Heqos'. clear Homatch.
      unfold is_lookbehind_tape in Hs.
      destruct Hs as [Hs1 Hs2].
      specialize (Hs2 start ltac:(lia)).
      destruct Hs2 as [Hs2  Hs3].
      rewrite <- match_not_match.
      rewrite <- Hs2.
      subst vs'.
      rewrite hd_error_nth_error in H2.
      rewrite nth_error_firstn in H2 by lia.
      rewrite <- nth_error_skipn in H2. simpl in H2.
      assert (@ij_error bool 𝛼 start ts = Some false). {
        rewrite transpose_spec with (len := length w + 1) by auto.
        unfold ij_error.
        rewrite <- Hvs.
        unfold valuation in H2. rewrite H2. auto.
      }
      unfold ij_error in H. unfold tape in Ht'. rewrite Ht' in H.
      rewrite H. discriminate.
Qed.


Lemma oracle_compose (r : @LRegex A) (w : list A) (vs : list valuation) :
  is_oval r w vs
  -> forall i,
  i <= length w
    -> match_regex r w 0 i
      <-> match_oregex (abstract r) (ofirstn i (w, vs)).
Proof.
  intros.
  pose proof (oracle_compose_aux r w 0 vs).
  unfold is_oval in H.
  unfold abstract.
  specialize (H1 H 0 i ltac:(lia)).
  rewrite oskipn0 in H1.
  auto.
Qed.

End Abstraction.