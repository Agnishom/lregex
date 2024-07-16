(**

This file contains the following:
  1. The [reverse : LRegex -> LRegex] function, which reverses a regular expression.
  2. The [reverse_match] lemma, which describes the relationship between [r : LRegex] and [reverse r] in terms of [match_regex].

*)

Require Import Lia.
Require Import Coq.Lists.List.


Require Import LRegex.
Require Import Equations.

Section Reverse.

Generalizable Variables A.
Variable (A : Type).

Fixpoint reverse (r : @LRegex A) : LRegex  :=
  match r with
   | Epsilon => Epsilon
   | CharClass c => CharClass c
   | Concat r1 r2 => Concat (reverse r2) (reverse r1)
   | Union r1 r2 => Union (reverse r1) (reverse r2)
   | Star r => Star (reverse r)
   | LookAhead r => LookBehind (reverse r)
   | LookBehind r => LookAhead (reverse r)
   | NegLookAhead r => NegLookBehind (reverse r)
   | NegLookBehind r => NegLookAhead (reverse r)
   end.

Lemma reverse_involutive (r : LRegex) :
  reverse (reverse r) = r.
Proof.
  induction r; simpl; congruence.
Qed.

Lemma reverse_match_aux (r : LRegex) :
  (forall w start delta, 
       start <= length w
    -> match_regex r w start delta
    -> match_regex (reverse r) (rev w) (length w - (start + delta)) delta)
  /\ (forall w start delta,
     start <= length w
  -> match_regex (reverse r) w start delta
  -> match_regex r (rev w) (length w - (start + delta)) delta).
Proof.
  induction r; simpl reverse; split; intros w start delta.
  - repeat rewrite match_eps_iff.
    auto.
  - repeat rewrite match_eps_iff.
    auto.
  - repeat rewrite match_class_iff.
  intro Hlen.
  intros [a [ba [Ha Hd]]].
  exists a. repeat split; auto.
  assert (start < length w).
  { apply nth_error_Some. unfold not. congruence. }
  apply nth_error_nth with (d := a) in Ha.
  rewrite <- Ha.
  rewrite nth_error_nth' with (d := a).
    + rewrite rev_nth by lia.
    now replace (length w - S (length w - (start + delta))) with start by lia.
    + rewrite rev_length. lia.
  - repeat rewrite match_class_iff.
  intro Hlen.
  intros [a [ba [Ha Hd]]].
  exists a. repeat split; auto.
  assert (start < length w).
  { apply nth_error_Some. unfold not. congruence. }
  apply nth_error_nth with (d := a) in Ha.
  rewrite <- Ha.
  rewrite nth_error_nth' with (d := a).
    + rewrite rev_nth by lia.
    now replace (length w - S (length w - (start + delta))) with start by lia.
    + rewrite rev_length. lia.
  - intro Hlen. intros.
  rewrite match_concat_iff in H.
  destruct H as [d1 [d2 [H1 [H2 H3]]]].
  rewrite match_concat_iff.
  pose proof (match_length _ _ _ _ _ H1) as Hlen1.
  pose proof (match_length _ _ _ _ _ H2) as Hlen2.
  apply IHr1 in H1. apply IHr2 in H2.
  exists d2, d1.
  subst.
  repeat split; [| | lia].
    + replace (start + (d1 + d2)) with (start + d1 + d2) by lia. apply H2.
    + replace (length w - (start + (d1 + d2)) + d2) with (length w - (start + d1)) by lia.
    apply H1.
    + lia.
    + assumption.
  - intro Hlen. intros.
  rewrite match_concat_iff in H.
  destruct H as [d1 [d2 [H1 [H2 H3]]]].
  rewrite match_concat_iff.
  pose proof (match_length _ _ _ _ _ H1) as Hlen1.
  pose proof (match_length _ _ _ _ _ H2) as Hlen2.
  apply IHr2 in H1. apply IHr1 in H2.
  exists d2, d1.
  subst.
  repeat split; [| | lia].
    + replace (start + (d1 + d2)) with (start + d1 + d2) by lia. apply H2.
    + replace (length w - (start + (d1 + d2)) + d2) with (length w - (start + d1)) by lia.
    apply H1.
    + lia.
    + assumption.
  - intro Hlen. intros.
  rewrite match_union_iff in H.
  destruct H as [H1 | H2]; rewrite match_union_iff.
    + apply IHr1 in H1. auto. lia.
    + apply IHr2 in H2. auto. lia.
  - intro Hlen. intros.
  rewrite match_union_iff in H.
  destruct H as [H1 | H2]; rewrite match_union_iff.
    + apply IHr1 in H1. auto. lia.
    + apply IHr2 in H2. auto. lia.
  - intro Hlen. remember (r *) as e.
  intro.
  induction H; try discriminate.
    + apply match_star_eps.
    +
    pose proof (match_length _ _ _ _ _ H) as Hlen1.
    pose proof (match_length _ _ _ _ _ H0) as Hlen2.
    inversion Heqe. subst.
    specialize (IHmatch_regex2 ltac:(lia) ltac:(reflexivity)).
    clear IHmatch_regex1.
    apply IHr in H.
    replace (d1 + d2) with (d2 + d1) at 2 by lia.  
    apply match_star_r.
    replace (start + (d1 + d2)) with (start + d1 + d2) by lia.
    apply IHmatch_regex2.
    replace (length w - (start + (d1 + d2)) + d2)
      with (length w - (start + d1)) by lia.
    apply H. lia.
  - intro Hlen.
    replace ((reverse r) *) with ((reverse (r *))) by auto.
    remember (reverse (r *)) as e. intro H.
    induction H; try discriminate.
    + apply match_star_eps.
    + subst.
    pose proof (match_length _ _ _ _ _ H) as Hlen1.
    pose proof (match_length _ _ _ _ _ H0) as Hlen2.
    inversion Heqe. subst.
    specialize (IHmatch_regex2 ltac:(lia) ltac:(reflexivity)).
    clear IHmatch_regex1.
    apply IHr in H.
    replace (d1 + d2) with (d2 + d1) at 2 by lia.  
    apply match_star_r.
    replace (start + (d1 + d2)) with (start + d1 + d2) by lia.
    apply IHmatch_regex2.
    replace (length w - (start + (d1 + d2)) + d2) with (length w - (start + d1)) by lia.
    apply H. lia.
  - rewrite match_lookahead_iff. rewrite match_lookbehind_iff.
    intro Hlen. intros [H1 H2].
    apply IHr in H1.
    subst. replace ((length w - (start + (length w - start))) ) with 0 in H1 by lia.
    replace (start + 0) with start by lia.
    auto. lia.
  - rewrite match_lookahead_iff. rewrite match_lookbehind_iff.
    intro Hlen. intros [H1 H2].
    apply IHr in H1.
    subst. simpl in H1.
    replace (start + 0) with start by lia.
    rewrite rev_length.
    pose proof (match_length _ _ _ _ _ H1) as Hlen1.
    rewrite rev_length in Hlen1.
    replace (length w - (length w - start)) with start by lia.
    auto. lia.
  - rewrite match_lookbehind_iff. rewrite match_lookahead_iff.
    intro Hlen. intros [H1 H2].
    pose proof (match_length _ _ _ _ _ H1) as Hlen1.
    apply IHr in H1.
    subst. replace ((length w - (start + (length w - start))) ) with 0 in H1 by lia.
    replace (start + 0) with start by lia. simpl in H1.
    rewrite rev_length.
    replace (length w - (length w - start)) with start by lia.
    auto. lia.
  - rewrite match_lookbehind_iff. rewrite match_lookahead_iff.
    intro Hlen. intros [H1 H2].
    apply IHr in H1.
    subst. 
    replace ((length w - (start + (length w - start))) ) with 0 in H1 by lia.
    replace (start + 0) with start by lia. auto. lia.
  - rewrite match_neglookahead_iff. rewrite match_neglookbehind_iff.
    repeat rewrite <- match_not_match.
    intro Hlen. intros [H1 H2].
    split; [ | auto].
    unfold not. intros H3.
    apply IHr in H3.
    rewrite rev_involutive in H3. rewrite rev_length in H3.
    simpl in H3. subst delta.
    replace (start + 0) with start in H3 by lia.
    replace (length w - (length w - start)) with start in H3 by lia.
    auto. rewrite rev_length. lia.
  - rewrite match_neglookahead_iff. rewrite match_neglookbehind_iff.
    repeat rewrite <- match_not_match.
    intro Hlen. intros [H1 H2].
    split; [ | auto].
    unfold not. intros H3.
    apply IHr in H3.
    rewrite rev_involutive in H3. rewrite rev_length in H3.
    simpl in H3. subst delta.
    replace (start + 0) with start in H3 by lia.
    replace (length w - (length w - start)) with start in H3 by lia.
    replace (length w - (length w - start + start)) with 0 in H3 by lia.
    auto. rewrite rev_length. lia.
  - rewrite match_neglookbehind_iff. rewrite match_neglookahead_iff.
    repeat rewrite <- match_not_match.
    intro Hlen. intros [H1 H2].
    split; [ | auto].
    unfold not. intros H3.
    apply IHr in H3.
    rewrite rev_involutive in H3. rewrite rev_length in H3.
    simpl in H3. subst delta.
    replace (start + 0) with start in H3 by lia.
    replace (length w - (length w - start)) with start in H3 by lia.
    replace (length w - (length w - start + start)) with 0 in H3 by lia.
    auto. rewrite rev_length. lia.
  - rewrite match_neglookbehind_iff. rewrite match_neglookahead_iff.
    repeat rewrite <- match_not_match.
    intro Hlen. intros [H1 H2].
    split; [ | auto].
    unfold not. intros H3.
    apply IHr in H3.
    rewrite rev_involutive in H3. rewrite rev_length in H3.
    simpl in H3. subst delta.
    replace (start + 0) with start in H3 by lia.
    replace (length w - (length w - start)) with start in H3 by lia.
    auto. rewrite rev_length. lia.
Qed. 

Lemma reverse_match1 :
  forall r w start delta,
    start <= length w
    -> match_regex r w start delta
    -> match_regex (reverse r) (rev w) (length w - (start + delta)) delta.
Proof.
  pose proof reverse_match_aux.
  firstorder.
Qed.

Lemma reverse_match :
  forall r w start delta,
    start <= length w
    -> start + delta <= length w
    -> match_regex r w start delta
    <-> match_regex (reverse r) (rev w) (length w - (start + delta)) delta.
Proof.
  intros r w start delta HX HY. split; intros H0.
  - now apply reverse_match1 in H0.
  - apply reverse_match1 in H0.
    rewrite rev_involutive in H0.
    rewrite rev_length in H0.
    rewrite reverse_involutive in H0.
    replace (length w - (length w - (start + delta) + delta))
      with start in H0 by lia.
    auto. rewrite rev_length. lia.
Qed.
    
End Reverse.

Arguments reverse {A}.