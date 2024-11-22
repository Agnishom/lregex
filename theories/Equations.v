(**

This file contains a number of useful lemmas and relations which allow equational reasoning on regular expressions.

  1. The [regex_eq : LRegex -> LRegex -> Prop] relation is an equivalence relation defined on regular expressions.
     - We use the notation [r1 ≡ r2] to denote that [r1] and [r2] are equivalent.
     - We prove that [regex_eq] is a congruence with respect to the regex constructors.
  2. The [regex_leq : LRegex -> LRegex -> Prop] relation is a partial order defined on regular expressions.
     - We use the notation [r1 ⊑ r2] to denote that whenever 
       [r1] matches [w] between [i, j], then so does [r2].
     - We prove that the regex constructors are monotonic with respect to [regex_leq].
  3. We prove a number of lemmas involving these relations.
     - This includes the Kleene Axioms
     - A number of identitites involving lookaheads and lookbehinds

*)

Require Import Lia.
Require Import Coq.Arith.Wf_nat.


Require Import Coq.Lists.List.

Require Export Setoid.
Require Import Morphisms Setoid.
Require Export Relation_Definitions.
Require Import Relation_Operators.
Require Import Operators_Properties.

Require Import LRegex.

Open Scope bool_scope.

Section Equations.

Context {A : Type}.

Definition regex_eq (r1 r2 : @LRegex A) : Prop :=
    forall w start delta,
        match_regex r1 w start delta <-> match_regex r2 w start delta.

Infix "≡" := regex_eq (at level 70, no associativity).

Definition regex_leq (r s : LRegex) : Prop :=
    r ∪ s ≡ s.

Notation "r ⊑ s" := (regex_leq r s) (at level 70).

Definition suffix_match (r : LRegex) (w : list A) (i : nat) : Prop :=
    match_regex r w i (length w - i).

Definition wildcard : (@LRegex A) := (CharClass (fun _ => true)) *.

Definition end_of_string : (@LRegex A) := 
    (?!> (CharClass (fun _ => true)) · wildcard).

Fixpoint regex_exp (r : LRegex) (n : nat) : (@LRegex A) :=
    match n with
    | 0 => Epsilon
    | S n' => r · (regex_exp r n')
    end.

Notation "r ^^ n" := (regex_exp r n) (at level 30).

Definition empty_reg : @LRegex A :=
    CharClass (fun _ => false).

Notation "∅" := empty_reg.

Lemma match_length : forall r (w : list A) start delta,
    match_regex r w start delta -> delta <= length w - start.
Proof.
    induction r; intros.
    - rewrite match_eps_iff in H. lia.
    - rewrite match_class_iff in H.
      destruct H as [a [Ha1 [Ha2 H1]]].
      assert (nth_error w start <> None) by congruence.
      apply nth_error_Some in H. lia.
    - rewrite match_concat_iff in H.
      destruct H as [d1 [d2 [H1 [H2 H3]]]].
      apply IHr1 in H1. apply IHr2 in H2. lia.
    - rewrite match_union_iff in H.
      destruct H as [H1 | H2].
      + apply IHr1 in H1. lia.
      + apply IHr2 in H2. lia.
    - remember (Star r) as r'.
      induction H; subst; try discriminate.
      + lia.
      + inversion Heqr'; subst.
        apply IHmatch_regex2 in Heqr'.
        apply IHr in H. lia.
    - rewrite match_lookahead_iff in H.
      lia.
    - rewrite match_lookbehind_iff in H.
      lia.
    - rewrite match_neglookahead_iff in H.
      lia.
    - rewrite match_neglookbehind_iff in H.
      lia.
Qed.

Instance regex_eq_refl : Reflexive regex_eq.
Proof.
    intros r. unfold regex_eq. tauto.
Qed.

Instance regex_eq_sym : Symmetric regex_eq.
Proof.
    intros r1 r2. unfold regex_eq. firstorder.
Qed.

Instance regex_eq_trans : Transitive regex_eq.
Proof.
    intros r1 r2 r3. unfold regex_eq. firstorder.
    + rewrite <- H0. rewrite <- H. auto.
    + rewrite H. rewrite H0. auto.
Qed.

Hint Resolve regex_eq_sym regex_eq_refl regex_eq_trans : regex.

Instance regex_eq_equiv : Equivalence regex_eq.
Proof.
    split; auto with regex.
Qed.

Hint Resolve regex_eq_equiv : regex.

Lemma concat_eps_l : forall (r : LRegex),
    Epsilon · r ≡ r.
Proof.
    unfold regex_eq. intros.
    rewrite match_concat_iff.
    split.
    + intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_eps_iff in H1.
      subst. now replace (start + 0) with start in H2 by lia.
    + intros. exists 0, delta.
       repeat split.
       - now apply match_eps_iff.
       - replace (start + 0) with start by lia. auto.
Qed.

Lemma concat_eps_r : forall (r : LRegex),
    r · Epsilon ≡ r.
Proof.
    unfold regex_eq. intros.
    rewrite match_concat_iff.
    split.
    + intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_eps_iff in H2.
      subst. now replace (d1 + 0) with d1 by lia.
    + intros. exists delta, 0.
       repeat split; [auto | | lia].
       - now apply match_eps_iff.
Qed.

Lemma concat_assoc : forall r1 r2 r3,
    (r1 · r2) · r3 ≡ r1 · (r2 · r3).
Proof.
    intros. unfold regex_eq. intros. 
    rewrite match_concat_iff. rewrite match_concat_iff.
    split.
    - intros [d12 [d3 [H1 [H2 H3]]]].
      rewrite match_concat_iff in H1.
      destruct H1 as [d1 [d2 [H1 [H4 H5]]]].
      exists d1, (d2 + d3).
      repeat split; [auto| |lia].
      rewrite match_concat_iff.
      exists d2, d3. 
      repeat split; auto.
      now replace (start + d1 + d2) with (start + d12) by lia.
    - intros [d1 [d23 [H1 [H2 H3]]]].
      rewrite match_concat_iff in H2.
      destruct H2 as [d2 [d3 [H2 [H4 H5]]]].
      exists (d1 + d2), d3.
      repeat split; [auto| |lia].
      rewrite match_concat_iff.
      exists d1, d2. 
      repeat split; auto.
      now replace (start + (d1 + d2)) with (start + d1 + d2) by lia.
Qed.

Hint Rewrite concat_eps_l concat_eps_r concat_assoc : regex.

Lemma union_assoc : forall (r1 r2 r3 : LRegex),
    (r1 ∪ r2) ∪ r3 ≡ r1 ∪ (r2 ∪ r3).
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_union_iff. 
    tauto.
Qed.

Lemma union_comm : forall (r1 r2 : LRegex),
    r1 ∪ r2 ≡ r2 ∪ r1.
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_union_iff. 
    tauto.
Qed.

Lemma union_idemp : forall (r : LRegex),
    r ∪ r ≡ r.
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_union_iff. 
    tauto.
Qed.

Hint Rewrite union_assoc union_comm union_idemp : regex.

Lemma concat_distrib_union_l : forall (r s t : LRegex),
   r · (s ∪ t) ≡ (r · s) ∪ (r · t).
Proof.
   unfold regex_eq. intros.
   rewrite match_concat_iff.
   rewrite match_union_iff.
   repeat rewrite match_concat_iff.
   split.
   - intros [d1 [d2 [H1 [H2 H3]]]].
     rewrite match_union_iff in H2.
     destruct H2 as [H2 | H2].
     + left. exists d1, d2. repeat split; auto.
     + right. exists d1, d2. repeat split; auto.
   - intros [H1 | H1].
     + destruct H1 as [d1 [d2 [H1 [H2 H3]]]].
       exists d1, d2. repeat split; auto.
       rewrite match_union_iff. auto.
     + destruct H1 as [d1 [d2 [H1 [H2 H3]]]].
       exists d1, d2. repeat split; auto.
       rewrite match_union_iff. auto.
Qed.

Lemma concat_distrib_union_r : forall (r s t : LRegex),
   (r ∪ s) · t ≡ (r · t) ∪ (s · t).
Proof.
    unfold regex_eq. intros.
    rewrite match_concat_iff.
    rewrite match_union_iff.
    repeat rewrite match_concat_iff.
    split.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_union_iff in H1.
      destruct H1 as [H1 | H1].
      + left. exists d1, d2. repeat split; auto.
      + right. exists d1, d2. repeat split; auto.
    - intros [H1 | H1].
      + destruct H1 as [d1 [d2 [H1 [H2 H3]]]].
         exists d1, d2. repeat split; auto.
         rewrite match_union_iff. auto.
      + destruct H1 as [d1 [d2 [H1 [H2 H3]]]].
         exists d1, d2. repeat split; auto.
         rewrite match_union_iff. auto.
Qed.

Hint Rewrite concat_distrib_union_l concat_distrib_union_r : regex.

Lemma lookahead_comm : forall (r1 r2 : LRegex),
    (?> r1) · (?> r2) ≡ (?> r2) · (?> r1).
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_concat_iff.
    split.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_lookahead_iff in H1.
      rewrite match_lookahead_iff in H2.
      destruct H1 as [H11 H12].
      destruct H2 as [H21 H22].
      subst. exists 0, 0.
      replace (start + 0) with start in * by lia.
      repeat rewrite match_lookahead_iff.
      firstorder.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_lookahead_iff in H1.
      rewrite match_lookahead_iff in H2.
      destruct H1 as [H11 H12].
      destruct H2 as [H21 H22].
      subst. exists 0, 0.
      replace (start + 0) with start in * by lia.
      repeat rewrite match_lookahead_iff.
      firstorder. 
Qed.

Lemma lookahead_star_eps : forall (r : LRegex),
    (?> r) * ≡ Epsilon.
Proof.
    unfold regex_eq. intros.
    rewrite match_eps_iff.
    split; intros.
    - remember ( (?> r) *) as e.
      induction H; inversion Heqe.
      split.
      subst.
      assert (d2 = 0) by now apply IHmatch_regex2.
      rewrite match_lookahead_iff in H.
      lia.
    - subst. constructor.
Qed.

Lemma lookahead_distrib_union : forall (r s : LRegex),
    (?> r) ∪ (?> s) ≡ (?> r ∪ s).
Proof.
    unfold regex_eq. intros.
    rewrite match_union_iff.
    repeat rewrite match_lookahead_iff.
    rewrite match_union_iff.
    tauto.
Qed.

Lemma lookahead_neglookahead_inverse : forall (r : LRegex),
    (?> r) ∪ (?!> r) ≡ Epsilon.
Proof.
    unfold regex_eq. intros.
    rewrite match_union_iff.
    pose proof match_lem r w start (length w - start) as [Hr | Hr];
        rewrite match_eps_iff;
        rewrite match_lookahead_iff;
        rewrite match_neglookahead_iff;
        rewrite <- match_not_match;
        firstorder.
Qed.

Hint Rewrite lookahead_comm lookahead_star_eps lookahead_distrib_union lookahead_neglookahead_inverse : regex.

Lemma lookahead_conj (r s : LRegex) :
    forall start w, 
        suffix_match ((?> r) · s) w start
        <-> (suffix_match r w start /\ suffix_match s w start).
Proof.
    intros. unfold suffix_match.
    rewrite match_concat_iff.
    split.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_lookahead_iff in H1.
      destruct H1 as [H11 H12].
      subst. simpl.
      replace (start + 0) with start in H2 by lia.
      simpl in H3. subst. auto.
    - intros [H1 H2].
       exists 0, (length w - start).
       replace (start + 0) with start by lia.
       simpl.
       repeat split; auto.
       + now constructor.
Qed.

Lemma wildcard_match : forall w start delta,
    delta <= length w - start
    -> match_regex wildcard w start delta.
Proof.
    intros w start delta. revert w start.
    induction delta.
    - constructor.
    - intros. replace (S delta) with (1 + delta) by lia.
      unfold wildcard.
      constructor.
      + eapply match_class; [auto | ].
        apply nth_error_nth'.
        lia.
      + apply IHdelta.
        lia.
        Unshelve. 
        destruct w eqn:E. simpl in H. lia.
        exact a.
Qed.

Lemma wildcard_match_iff : forall w start delta,
    delta <= length w - start
    <-> match_regex wildcard w start delta.
Proof.
  split.
  - apply wildcard_match.
  - apply match_length.
Qed.

Lemma lookahead_flatten_wildcard : forall (r s: LRegex),
    (?> r · (?> s) · wildcard) ≡ (?> r · s).
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_lookahead_iff.
    repeat rewrite match_concat_iff.
    split.
    - intros [[d1 [d2 [H1 [H2 H3]]]] Hdelta].
      rewrite match_concat_iff in H2.
      destruct H2 as [d3 [d4 [H2 [H4 H5]]]].
      rewrite match_lookahead_iff in H2.
      destruct H2 as [H2 H6].
      subst. split; [| auto].
      exists d1, (length w - (start + d1)).
      repeat split; auto.
      lia.
    - intros [[d1 [d2 [H1 [H2 H3]]]] Hdelta].
      split; [| auto].
      exists d1, (length w - (start + d1)).
      split; [auto | split; [ | lia]].
      apply lookahead_conj. split.
      + unfold suffix_match.
        replace (length w - (start + d1)) with d2 by lia.
        auto.
      + apply wildcard_match. lia.
Qed.

Lemma lookahead_flatten : forall (r s: LRegex),
    (?> (?> r) · s) ≡ (?> r) · (?> s).
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_lookahead_iff.
    repeat rewrite match_concat_iff.
    split.
    - intros [[d1 [d2 [H1 [H2 H3]]]] Hdelta].
      subst delta.
      exists 0, 0.
      simpl.
      repeat rewrite match_lookahead_iff.
      rewrite match_lookahead_iff in H1.
      destruct H1 as [H1 H4].
      subst d1. simpl in H3. subst d2.
      replace (start + 0) with start in * by lia.
      auto.
    - intros [d1 [d2 [Hr [Hs Hd]]]].
      rewrite match_lookahead_iff in Hr.
      rewrite match_lookahead_iff in Hs.
      destruct Hr as [Hr Hr'].
      destruct Hs as [Hs Hs'].
      subst. split; auto.
      exists 0, (length w - start).
      rewrite match_lookahead_iff.
      replace (start + 0) with start in * by lia.
      split; auto.
Qed.

Lemma lookahead_neglookahead_eps (r : LRegex) :
    (?> r) ∪ (?!> r) ≡ Epsilon.
Proof.
    unfold regex_eq. intros.
    rewrite match_union_iff.
    pose proof match_lem  r w start (length w - start) as [Hr | Hr];
        rewrite match_eps_iff;
        rewrite match_lookahead_iff;
        rewrite match_neglookahead_iff;
        rewrite <- match_not_match;
        firstorder.
Qed.

Lemma lookahed_neglookahead_concat (r s : LRegex) :
    (?> (?!> r) · s) ≡ (?!> r) · (?> s).
Proof.
  unfold regex_eq. intros.
  rewrite match_concat_iff.
  rewrite match_lookahead_iff.
  rewrite match_concat_iff.
  split.
  - intros [[d1 [d2 [H1 [H2 H3]]]] Hdelta].
    subst delta.
    exists 0, 0.
    rewrite match_neglookahead_iff in H1.
    destruct H1 as [H1 H4].
    subst d1. simpl in *. subst d2.
    repeat split.
    + rewrite match_neglookahead_iff.
      split; auto.
    + replace (start + 0) with start in * by lia.
      rewrite match_lookahead_iff.
      split; auto.
  - intros [d1 [d2 [H1 [H2 H3]]]].
    rewrite match_neglookahead_iff in H1.
    rewrite match_lookahead_iff in H2.
    destruct H1 as [H1 H4].
    destruct H2 as [H2 H5].
    subst. split; [ | auto].
    exists 0, (length w - start).
    repeat split.
    + rewrite match_neglookahead_iff.
      split; auto.
    + replace (start + 0) with start in * by lia.
      auto.
Qed.


Lemma neglookahead_union (r s : LRegex) :
    (?!> (?> r) · s) ≡ (?!> r) ∪ (?!> s).
Proof.
  unfold regex_eq. intros.
  rewrite match_union_iff.
  rewrite match_neglookahead_iff.
  rewrite not_match_concat_iff.
  repeat rewrite match_neglookahead_iff.
  split.
  - intros [H Hdelta]. subst delta.
    specialize (H 0 ltac:(lia)).
    destruct H.
    + rewrite not_match_lookahead_iff in H.
      destruct H; [ | congruence].
      tauto.
    + replace (start + 0) with start in H by lia.
      replace (length w - start - 0) with (length w - start) in H by lia.
      tauto.
  - intros [[H Hd] | [H Hd]]; subst delta.
    + split; [ | auto]. 
      intros d Hd.
      rewrite not_match_lookahead_iff.
      tauto.
    + split; [ | auto]. 
      intros d Hd.
      assert (d = 0 \/ d <> 0) as [Hd' | Hd'] by lia.
      * subst. replace (start + 0) with start by lia.
        replace (length w - start - 0) with (length w - start) by lia.
        auto.
      * left. rewrite not_match_lookahead_iff.
        right. auto.
Qed.

Lemma double_neglookahead_lookahead (r : LRegex) :
    (?!> (?!> r · wildcard) · wildcard) ≡ (?> r · wildcard).
Proof.
  unfold regex_eq. intros.
  split.
  - intros.
    rewrite match_lookahead_iff.
    rewrite match_neglookahead_iff in H.
    rewrite not_match_concat_iff in H.
    destruct H.
    subst delta. split; [ | auto].
    rewrite match_concat_iff.
    specialize (H 0 ltac:(lia)).
    destruct H as [H | H].
    + rewrite not_match_neglookahead_iff in H.
      destruct H ; [ | congruence].
      rewrite match_concat_iff in H.
      auto.
    + rewrite <- match_not_match in H. 
      replace (start + 0) with start in H by lia.
      replace (length w - start - 0) with (length w - start) in H by lia.
      pose proof wildcard_match w start (length w - start) ltac:(lia) as Hwild.
      contradiction.
  - intros.
    rewrite match_neglookahead_iff.
    rewrite not_match_concat_iff.
    rewrite match_lookahead_iff in H.
    rewrite match_concat_iff in H.
    destruct H as [[d1 [d2 [H1 [H2 H3]]]] Hd].
    subst delta.
    split; [ | auto].
    intros d Hd.
    rewrite not_match_neglookahead_iff.
    left.
    rewrite match_concat_iff. left.
    exists d1, d2.
    tauto.
Qed.

Lemma neglookahead_unsat (r : LRegex) :
    (forall w start delta, ~ match_regex r w start delta)
    -> (?> r) ≡ r.
Proof.
    intros Hunsat.
    unfold regex_eq. intros.
    rewrite match_lookahead_iff.
    split; intros.
    - destruct H. specialize (Hunsat w start (length w - start)).
      contradiction.
    - specialize (Hunsat w start delta).
      contradiction.
Qed.


Lemma lookahead_neglookahed_union (r s : LRegex) :
    (?!> (?!> r) · s) ≡ (?> r) ∪ (?!> s).
Proof.
  unfold regex_eq. intros.
  rewrite match_union_iff.
  rewrite match_lookahead_iff.
  repeat rewrite match_neglookahead_iff.
  rewrite not_match_concat_iff.
  split.
  - intros [H Hdelta]. subst delta.
    specialize (H 0 ltac:(lia)).
    rewrite not_match_neglookahead_iff in H.
    replace (start + 0) with start in H by lia.
    replace (length w - start - 0) with (length w - start) in H by lia.
    tauto.
  - intros [[H Hd] | [H Hd]]; subst delta.
    + split; [ | auto]. 
      intros d Hd.
      rewrite not_match_neglookahead_iff.
      tauto.
    + split; [ | auto]. 
      intros d Hd.
      assert (d = 0 \/ d <> 0) as [Hd' | Hd'] by lia.
      * subst. replace (start + 0) with start by lia.
        replace (length w - start - 0) with (length w - start) by lia.
        auto.
      * left. rewrite not_match_neglookahead_iff.
        right. auto.
Qed. 

Lemma lookahead_neglookahead_not_match (r : @LRegex A) :
    forall w start delta, 
        ~ match_regex ((?> r) · (?!> r)) w start delta.
Proof.
    intros w start delta.
    unfold not.
    rewrite match_concat_iff.
    intros [d1 [d2 [H1 [H2 H3]]]].
    rewrite match_lookahead_iff in H1.
    rewrite match_neglookahead_iff in H2.
    rewrite <- match_not_match in H2.
    destruct H1 as [H1 H4].
    destruct H2 as [H2 H5].
    subst. replace (start + 0) with start in H2 by lia.
    auto.
Qed.

Lemma peel_lookahead (p1 p2 : A -> bool) (r1 r2 : LRegex) :
    (?> (CharClass p1) · r1) · (CharClass p2) · r2
        ≡ (CharClass (fun c => p1 c && p2 c)) · (?> r1 ) · r2.
Proof.
    unfold regex_eq. intros.
    repeat rewrite match_concat_iff.
    split.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_concat_iff in H2.
      destruct H2 as [d3 [d4 [H2 [H4 H5]]]].
      rewrite match_lookahead_iff in H1.
      destruct H1 as [H1 H6].
      subst d1. simpl in H3.
      rewrite match_concat_iff in H1.
      destruct H1 as [d5 [d6 [H1 [H7 H8]]]].
      rewrite match_class_iff in H1.
      destruct H1 as [a [Ha [Haa Hd5]]].
      rewrite match_class_iff in H2.
      destruct H2 as [b [Hb [Hbb Hd6]]].
      subst d3 d5.
      replace (start + 0) with start in * by lia.
      assert (a = b).
      { rewrite Haa in Hbb. inversion Hbb. auto. }
      subst b.
      exists 1, (0 + d4).
      repeat split; [ | | lia].
      + apply match_class with (a := a).
        rewrite Bool.andb_true_iff; auto.
        auto.
     + apply match_concat.
       * apply match_lookahead.
         replace (length w - (start + 1)) with d6 by lia.
         auto.
       * replace (start + 1 + 0) with (start + 1) by lia.
         auto.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      exists 0, delta.
      rewrite match_concat_iff in H2. 
      destruct H2 as [d3 [d4 [H2 [H4 H5]]]].
      rewrite match_lookahead_iff in H2.
      destruct H2 as [H2 H6].
      subst d3. simpl in H5. subst d4.
      replace (start + d1 + 0) with (start + d1) in H4 by lia.
      rewrite match_class_iff in H1.
      destruct H1 as [a [Ha [Haa Hd1]]].
      subst d1. rewrite Bool.andb_true_iff in Ha.
      destruct Ha as [Ha1 Ha2].
      repeat split.
      + apply match_lookahead.
        assert (start < length w). {
            apply nth_error_Some.
            destruct (nth_error w start) eqn:Hnth;
                inversion Haa; discriminate.
        }
        replace (length w - start) with (1 + (length w - (start + 1))) by lia.
        apply match_concat; [ | auto].
        apply match_class with (a := a); auto.
      + replace (start + 0) with start by lia.
        rewrite H3.
        apply match_concat; [ | auto].
        now apply match_class with (a := a).
Qed.

Hint Rewrite lookahead_flatten_wildcard lookahead_flatten lookahead_neglookahead_eps
             peel_lookahead : regex.
Hint Resolve lookahead_neglookahead_not_match : regex.

Lemma match_star_r (r : LRegex) (w : list A) (start : nat) (d1 d2 : nat) :
    match_regex (r *) w start d1
    -> match_regex r w (start + d1) d2
    -> match_regex (r *) w start (d1 + d2).
Proof.
    intros Hmatch. remember (r *) as e.
    revert d2. induction Hmatch; intros; inversion Heqe.
    - replace (start + 0) with start in H by lia.
      replace (0 + d2) with (d2 + 0) by lia.
      constructor. auto. constructor.
    - subst. replace (d1 + d2 + d0) with (d1 + (d2 + d0)) by lia.
      constructor. auto. 
      apply IHHmatch2. auto.
      replace (start + (d1 + d2)) with (start + d1 + d2) in H by lia.
      auto.
Qed.

Lemma lookahead_eps_concat (r : @LRegex A): 
    forall w start delta,
    match_regex ((?> Epsilon) · r) w start delta
    -> match_regex ((?> Epsilon)) w start delta.
Proof.
    intros w start delta.
    rewrite match_concat_iff.
    rewrite match_lookahead_iff.
    rewrite match_eps_iff.
    intros [d1 [d2 [H1 [H2 H3]]]].
      rewrite match_lookahead_iff in H1.
      destruct H1 as [H1 H4].
      subst d1. simpl in H3.
      rewrite match_eps_iff in H1.
      apply match_length in H2. lia.
Qed.

Lemma lookahead_eps_eps :
    ((?> Epsilon) · Epsilon) ≡ (?> Epsilon).
Proof.
    unfold regex_eq. split.
    - apply lookahead_eps_concat.
    - rewrite match_concat_iff. 
      rewrite match_lookahead_iff.
      rewrite match_eps_iff.
      intros [H1 H2]. subst.
      exists 0, 0. repeat split.
      + apply match_lookahead.
        rewrite H1. constructor.
      + constructor.
Qed.

Lemma lookahead_eps_charclass (p : A -> bool) (r : @LRegex A) :
    forall w start delta,
      not_match_regex ((?> Epsilon) · (CharClass p) · r) w start delta.
Proof.
    intros.
    rewrite <- match_not_match.
    unfold not. intros.
    rewrite match_concat_iff in H.
    destruct H as [d1 [d2 [H [H1 H2]]]].
    rewrite match_lookahead_iff in H.
    rewrite match_concat_iff in H1.
    destruct H1 as [d3 [d4 [H3 [H4 H5]]]].
    rewrite match_class_iff in H3.
    destruct H as [H H6].
    destruct H3 as [a [Ha [Haa H3]]].
    subst d1 d3.
    rewrite match_eps_iff in H.
    replace (start + 0) with start in Haa by lia.
    assert (start < length w). {
        apply nth_error_Some.
        destruct (nth_error w start) eqn:Hnth;
            inversion Haa; discriminate.
    }
    lia.
Qed.

Lemma end_of_string_match : forall w start delta,
    match_regex end_of_string w start delta
    <-> delta = 0 /\ start >= length w.
Proof.
  unfold end_of_string. intros.
  rewrite match_neglookahead_iff.
  rewrite not_match_concat_iff.
  split.
  - intros [H Hd]. subst. split; [ auto | ].
    assert (length w > start \/ length w <= start) as [Hd | Hd] by lia.
    + specialize (H 1 ltac:(lia)).
      destruct H.
      * rewrite not_match_class_iff in H.
        destruct H. congruence.
        destruct H. rewrite nth_error_None in H. lia.
        destruct H. destruct H. congruence.
      * rewrite <- match_not_match in H.
        pose proof wildcard_match w (start + 1) (length w - (start + 1)) ltac:(auto) as Hwild.
        replace (length w - (start + 1)) with (length w - start - 1) in Hwild by lia.
        contradiction.
    + lia.
  - intros [Hdelta Hstart]. subst.
    split; [ | auto].
    intros d Hd.
    assert (d = 0) by lia. subst.
    left.
    rewrite not_match_class_iff.
    left. discriminate.
Qed.
    
Hint Rewrite lookahead_eps_eps : regex.

Lemma unmatch_star_r (r : LRegex) (w : list A) (start delta : nat) :
    match_regex (r *) w start delta
    -> (delta = 0 \/
        exists d1 d2, d1 + d2 = delta
        /\ match_regex (r *) w start d1
        /\ match_regex r w (start + d1) d2).
Proof.
    intros. remember (r *) as e.
    induction H; inversion Heqe.
    - auto.
    - subst. right.
      assert (r * = r *) by auto.
      apply IHmatch_regex2 in H1.
      destruct H1 as [H1 | [d3 [d4 [H1 [H2 H3]]]]].
      + subst. exists 0, d1. repeat split; auto.
        * constructor.
        * replace (start + 0) with start by lia.
          auto.
      + exists (d1 + d3), d4.
        repeat split; auto.
        * lia.
        * constructor; auto.
        * replace (start + (d1 + d3)) with (start + d1 + d3) by lia.
          auto. 
Qed.

Lemma match_star_r_iff (r : LRegex) (w : list A) (start : nat) (delta : nat) :
    match_regex (r *) w start delta
    <-> (delta = 0 \/
        exists d1 d2, d1 + d2 = delta
        /\ match_regex (r *) w start d1
        /\ match_regex r w (start + d1) d2).
Proof.
    split; [apply unmatch_star_r | ].
    intros [H1 | [d1 [d2 [H1 [H2 H3]]]]].
    - subst. constructor.
    - rewrite <- H1. now apply match_star_r.
Qed.

Lemma match_star_app (r : LRegex) (w : list A) (start d1 d2 : nat) :
    match_regex (r *) w start d1
    -> match_regex (r *) w (start + d1) d2
    -> match_regex (r *) w start (d1 + d2).
Proof.
    intros Hmatch. remember (r *) as e.
    revert d2. induction Hmatch; intros; inversion Heqe.
    - replace (start + 0) with start in H by lia.
      replace (0 + d2) with d2 by lia.
      subst. auto.
    - subst. replace (d1 + d2 + d0) with (d1 + (d2 + d0)) by lia. 
      constructor. auto. 
      apply IHHmatch2. auto.
      replace (start + (d1 + d2)) with (start + d1 + d2) in H by lia.
      apply H.
Qed.

Lemma match_star_once (r : LRegex) (w : list A) (start d : nat) :
    match_regex r w start d
    -> match_regex (r *) w start d.
Proof.
    intros Hmatch.
    replace d with (d + 0) by lia.
    constructor. auto. constructor.
Qed.

Hint Resolve match_star_once match_star_app : regex.

Lemma star_idemp : forall (r : LRegex),
    r * * ≡ r *.
Proof.
    unfold regex_eq. intros.
    split; intros.
    - remember (r * *) as e.
      induction H; inversion Heqe.
      + subst. constructor.
      + subst. apply match_star_app.
        * apply H.
        * apply IHmatch_regex2.
          auto.
    - replace delta with (delta + 0) by lia. 
      constructor; [auto | constructor].
Qed.



Instance regex_leq_refl : Reflexive regex_leq.
Proof.
    unfold regex_leq.
    auto using union_idemp.
Defined.

Instance union_proper : Proper (regex_eq ==> regex_eq ==> regex_eq) Union.
Proof.
    unfold regex_eq.
    intros r1 r2 Hr s1 s2 Hs.
    intros w start delta.
    repeat rewrite match_union_iff.
    firstorder.
Defined.

Instance concat_proper : Proper (regex_eq ==> regex_eq ==> regex_eq) Concat.
Proof.
    unfold regex_eq.
    intros r1 r2 Hr s1 s2 Hs.
    intros w start delta.
    repeat rewrite match_concat_iff.
    split.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      exists d1, d2.
      repeat split; [ | | auto].
      + apply Hr. auto.
      + apply Hs. auto.
    - intros [d1 [d2 [H1 [H2 H3]]]].
      exists d1, d2.
      repeat split; [ | | auto].
      + apply Hr. auto.
      + apply Hs. auto.
Defined.

Instance star_proper : Proper (regex_eq ==> regex_eq) Star.
Proof.
    assert (
    (forall (r1 r2 : LRegex), 
        (forall (w : list A) (start delta : nat),  
            match_regex r1 w start delta -> match_regex r2 w start delta)
    -> forall w start delta,
        match_regex (r1 *) w start delta -> match_regex (r2 *) w start delta)).
    { intros r1 r2 Hmatch w start delta.
      remember (r1 *) as e.
      induction 1; inversion Heqe.
      - subst. constructor.
      - subst. constructor.
        + auto.
        + apply IHmatch_regex2. auto.
    }
    unfold regex_eq.
    intros r1 r2 Hr.
    intros w start delta. 
    split;
        apply H; apply Hr.
Defined.

Instance lookahead_proper : Proper (regex_eq ==> regex_eq) LookAhead.
Proof.
    unfold regex_eq.
    intros r s H w start delta.
    rewrite !match_lookahead_iff.
    now rewrite H.
Defined.

Instance neglookahead_proper : Proper (regex_eq ==> regex_eq) NegLookAhead.
Proof.
    unfold regex_eq.
    intros r s H w start delta.
    rewrite !match_neglookahead_iff, <- !match_not_match.
    now rewrite H.
Defined.

Instance lookbehind_proper : Proper (regex_eq ==> regex_eq) LookBehind.
Proof.
    unfold regex_eq.
    intros r s H w start delta.
    rewrite !match_lookbehind_iff.
    now rewrite H.
Defined.

Instance neglookbehind_proper : Proper (regex_eq ==> regex_eq) NegLookBehind.
Proof.
    unfold regex_eq.
    intros r s H w start delta.
    rewrite !match_neglookbehind_iff, <- !match_not_match.
    now rewrite H.
Defined.


Hint Resolve union_proper concat_proper star_proper 
  lookahead_proper neglookahead_proper lookbehind_proper neglookbehind_proper
    : regex.

Instance regex_leq_trans : Transitive regex_leq.
Proof.
    unfold regex_leq.
    intros r s t.
    intros Hrs Hst.
    rewrite <- Hst.
    rewrite <- union_assoc.
    rewrite Hrs. reflexivity.
Defined.

Instance regex_leq_antisym : Antisymmetric _ regex_eq regex_leq.
Proof.
    unfold regex_leq.
    intros r s Hrs Hsr.
    rewrite <- Hrs.
    rewrite <- Hsr at 1.
    auto using union_comm.
Defined.

Instance regex_leq_preorder : PreOrder regex_leq.
Proof.
    split; auto with typeclass_instances.
Defined.

Instance regex_leq_partialorder : PartialOrder regex_eq regex_leq.
Proof.
    intros r s. simpl.
    split; intros.
    - split.
      + unfold regex_leq.
        rewrite H. auto using union_idemp.
      + unfold regex_leq.
        unfold Basics.flip.
        rewrite H. auto using union_idemp.
    - destruct H. unfold Basics.flip in H0.
      apply regex_leq_antisym; auto.
Defined.

Lemma subset_leq : forall (r s : LRegex),
    (forall (w : list A) (start delta : nat),
        match_regex r w start delta -> match_regex s w start delta)
    <-> r ⊑ s.
Proof.
    intros r s.
    unfold regex_leq.
    unfold regex_eq.
    split.
    - intros H w start delta.
      rewrite match_union_iff.
      firstorder.
    - intros H w start delta Hr.
      apply H. rewrite match_union_iff.
      firstorder. 
Qed.

Hint Resolve subset_leq : regex.


Lemma kleene_1 : forall (r : LRegex),
    Epsilon ∪ (r · r *) ⊑ r *.
Proof.
    intro r.
    apply subset_leq with (s := r *).
    intros w start delta H.
    inversion H.
    - subst. apply match_eps_iff in H5.
      subst. constructor.
    - inversion H5. subst.
      constructor; auto.
Qed.

Lemma kleene_2 : forall (r : LRegex),
    Epsilon ∪ (r * · r) ⊑ r *.
Proof.
    intro r.
    apply subset_leq with (s := r *).
    intros w start delta H.
    inversion H.
    - subst. apply match_eps_iff in H5.
      subst. constructor.
    - inversion H5. subst.
      apply match_star_r; auto.
Qed.

Lemma kleene_3_alt : forall (a b c : LRegex),
    (a · c) ∪ b ⊑ c -> (a *) · b ⊑ c.
Proof.
    intros a b c.
    repeat rewrite <- subset_leq.
    intros H w start delta Hconcat.
    inversion Hconcat. subst.
    clear Hconcat. revert H6. revert d2.
    remember (a *) as e. 
    induction H2; try discriminate.
    - intros. simpl. apply H.
      apply match_union_r. 
      replace (start + 0) with start in H6 by lia.
      auto.
    - intros. apply H.
      apply match_union_l.
      inversion Heqe. subst.
      replace (d1 + d2 + d0) with (d1 + (d2 + d0)) by lia.
      apply match_concat; auto.
      apply IHmatch_regex2; auto.
      now replace (start + d1 + d2) with (start + (d1 + d2)) by lia.
Qed.

Lemma kleene_3 : forall (r s : LRegex),
    r · s ⊑ s -> (r *) · s ⊑ s.
Proof.
    intros r s.
    repeat rewrite <- subset_leq.
    intros H w start delta Hconcat.
    inversion Hconcat. subst.
    clear Hconcat. revert H6. revert d2.
    remember (r *) as e. 
    induction H2; try discriminate.
    - intros. simpl.
      now replace (start + 0) with start in H6 by lia.
    - intros. inversion Heqe. subst.
        replace (d1 + d2 + d0) with (d1 + (d2 + d0)) by lia.
        apply H.
        apply match_concat; auto.
        apply IHmatch_regex2; auto.
        now replace (start + d1 + d2) with (start + (d1 + d2)) by lia.
Qed.

Lemma kleene_4 : forall (r s : LRegex),
    r · s ⊑ r -> r · (s *) ⊑ r.
Proof.
    intros r s H.
    apply subset_leq.
    intros w start delta HH.
    inversion HH. subst. clear HH.
    generalize dependent d1.
    induction d2 using lt_wf_ind.
    intros.
    apply match_star_nonempty in H6.
    destruct H6 as [Hd2 | [ds [X1 [X2 [X3 X4]]]]].
    - subst.
      now replace (d1 + 0) with d1 by lia.
    - replace (d1 + d2) with ((d1 + ds) + (d2 - ds)) by lia.
      apply H0.
      + lia.
      + apply H. apply match_union_l.
        apply match_concat; auto.
      + now replace (start + d1 + ds) with (start + (d1 + ds)) in X4 by lia.
Qed.

Lemma star_expand_l : forall (r : LRegex),
    r * ≡ Epsilon ∪ (r · r *).
Proof.
    intros r.
    apply regex_leq_antisym.
    - apply subset_leq.
      intros w start delta H.
      inversion H.
      + apply match_union_l. constructor.
      + apply match_union_r. apply match_concat; auto.
    - apply kleene_1.
Qed.

Lemma star_expand_r : forall (r : LRegex),
    r * ≡ Epsilon ∪ (r * · r).
Proof.
    intros r.
    apply regex_leq_antisym.
    - apply subset_leq.
      intros w start delta H.
      apply unmatch_star_r in H.
      destruct H as [Hd | [d1 [d2 [H1 [H2 H3]]]]].
        + apply match_union_l. subst; constructor.
        + apply match_union_r.
          rewrite <- H1. apply match_concat; auto.
    - apply kleene_2.
Qed.

Lemma star_exp (r : LRegex) :
    forall n, r ^^ n ⊑ r *.
Proof.
    intro.
    apply subset_leq.
    induction n.
    - simpl.
    intros w start delta H.
    apply match_eps_iff in H.
    subst. constructor.
    -  simpl.
    intros w start delta H.
    inversion H. subst.
    apply IHn in H6.
    constructor; auto.
Qed. 

Instance union_monotone : Proper (regex_leq ==> regex_leq ==> regex_leq) Union.
Proof.
    intros r1 r2 Hr s1 s2 Hs.
    unfold regex_leq in *.
    rewrite union_assoc.
    rewrite <- union_assoc with (r2 := r2).
    rewrite union_comm with (r1 := s1) at 1.
    rewrite <- union_assoc.
    rewrite <- union_assoc. rewrite Hr.
    rewrite union_assoc. rewrite Hs.
    reflexivity.
Qed.

Instance concat_monotone : Proper (regex_leq ==> regex_leq ==> regex_leq) Concat.
Proof.
    intros r1 r2 Hr s1 s2 Hs.
    rewrite <- subset_leq in Hr, Hs.
    apply subset_leq.
    intros w start delta H.
    inversion H.
    apply match_concat; auto.
Qed.

Lemma empty_reg_never : forall w i d,
    ~ match_regex ∅ w i d.
Proof.
    intros.
    unfold empty_reg.
    rewrite match_class_iff.
    intros [a [H _]].
    discriminate.
Qed.

Lemma union_empty_l : forall (r : @LRegex A),
  ∅ ∪ r ≡ r.
Proof.
    unfold regex_eq. intros.
    rewrite match_union_iff.
    split; auto.
    intros [H | H]; [ | auto].
    apply empty_reg_never in H. contradiction.
Qed.

Lemma union_empty_r : forall (r : @LRegex A),
    r ∪ ∅ ≡ r.
Proof.
  intros.
  rewrite union_comm.
  apply union_empty_l.
Qed.

End Equations.