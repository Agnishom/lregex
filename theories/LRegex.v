(**

This file contains the following:
    1. Syntax for regular expressions [LRegex : Type]
    2. Semantics for regular expressions [match_regex : LRegex -> list A -> nat -> nat -> Prop]. 
       - Note that the notation is supposed to be read as [match_regex r w start delta] which means 
         that [r] matches [w] between [start] and [start + delta].
    3. The predicate [not_match_regex : LRegex -> list A -> nat -> nat -> Prop] which is the negation of [match_regex]. 
       - A proposition [match_not_match] shows that [not_match_regex] is the negation of [match_regex].
       - A proposition [match_lem] showing that given any regular expression and positions, either [match_regex] or [not_match_regex] holds.
    4. The predicate [is_tape : LRegex -> list A -> list bool -> Prop]. We say that [t : list bool] is a tape for [r : LRegex] and [w : list A]
       if the i-th element of [t] is true if and only if [match_regex r w 0 i].
    5. The predicate [is_scanMatcher : (LRegex -> list A -> list bool) -> Prop ]. We say that [f : LRegex -> list A -> list bool] is a scanMatcher
       if for any regular expression [r : LRegex] and any word [w : list A], [f r w] is a tape for [r] and [w].
    6. A number of lemmas such as [match_eps_iff], [match_concat_iff], [match_star_iff], etc that are useful in manipulating the
       [match_regex] predicate.

*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Wf_nat.
Require Import Lia.


Declare Scope regex_scope.
Open Scope regex_scope.

Section Syntax.

Context {A : Type}.

Inductive LRegex : Type :=
| Epsilon : LRegex
| CharClass : (A -> bool) -> LRegex
| Concat : LRegex -> LRegex -> LRegex
| Union : LRegex -> LRegex -> LRegex
| Star : LRegex -> LRegex
| LookAhead : LRegex -> LRegex
| LookBehind : LRegex -> LRegex
| NegLookAhead : LRegex -> LRegex
| NegLookBehind : LRegex -> LRegex.

End Syntax.

Definition ε {A : Type} := @Epsilon A.
Infix "·" := Concat (at level 60, right associativity) : regex_scope.
Infix "∪" := Union (at level 50, left associativity) : regex_scope.
Notation "r *" := (Star r) (at level 40, no associativity) : regex_scope.

Notation "(?> r )" := (LookAhead r) (at level 40, no associativity) : regex_scope.
Notation "(?!> r )" := (NegLookAhead r) (at level 40, no associativity) : regex_scope.
Notation "(?< r )" := (LookBehind r) (at level 40, no associativity) : regex_scope.
Notation "(?<! r )" := (NegLookBehind r) (at level 40, no associativity) : regex_scope.

Section Semantics.

Context {A : Type}.

Inductive match_regex : LRegex -> list A -> nat -> nat -> Prop :=
| match_epsilon : forall (w : list A) (start : nat), 
    match_regex ε w start 0
| match_class : forall (a : A) (pred : A -> bool) (w : list A) (start : nat),
    (pred a = true) -> (nth_error w start = Some a) -> match_regex (CharClass pred) w start 1
| match_concat : forall (r1 r2 : LRegex) (w : list A) (start d1 d2 : nat),
    match_regex r1 w start d1 -> match_regex r2 w (start + d1) d2 
    -> match_regex (r1 · r2) w start (d1 + d2)
| match_union_l : forall (r1 r2 : LRegex) (w : list A) (start d : nat),
    match_regex r1 w start d -> match_regex (r1 ∪ r2) w start d
| match_union_r : forall (r1 r2 : LRegex) (w : list A) (start d : nat),
    match_regex r2 w start d -> match_regex (r1 ∪ r2) w start d
| match_star_eps : forall (r : LRegex) (w : list A) (start : nat),
    match_regex (r *) w start 0
| match_star : forall (r : LRegex) (w : list A) (start d1 d2 : nat), 
    match_regex r w start d1 -> match_regex (r *) w (start + d1) d2 
    -> match_regex (r *) w start (d1 + d2)
| match_lookahead : forall (r : LRegex) (w : list A) (start : nat),
   match_regex r w start (length w - start) -> match_regex ( (?> r) ) w start 0
| match_lookbehind : forall (r : LRegex) (w : list A) (start : nat),
    match_regex r w 0 start -> match_regex ((?< r)) w start 0
| match_neglookahead : forall (r : LRegex) (w : list A) (start : nat),
    not_match_regex r w start (length w - start) -> match_regex ( (?!> r) ) w start 0
| match_neglookbehind : forall (r : LRegex) (w : list A) (start : nat),
    not_match_regex r w 0 start -> match_regex ((?<! r)) w start 0
with not_match_regex : LRegex -> list A -> nat -> nat -> Prop :=
| not_match_epsilon : forall (w : list A) (start delta : nat),
    (delta <> 0) -> not_match_regex ε w start delta
| not_match_class_false : forall (a : A) (pred : A -> bool) (w : list A) (start delta: nat),
    (pred a = false) -> (nth_error w start = Some a) -> not_match_regex (CharClass pred) w start delta
| not_match_class_index : forall (pred : A -> bool) (w : list A) (start delta : nat),
    (nth_error w start = None) -> not_match_regex (CharClass pred) w start delta
| not_match_class_length : forall (pred : A -> bool) (w : list A) (start delta : nat),
    (delta <> 1) -> not_match_regex (CharClass pred) w start delta
| not_match_concat : forall (r1 r2 : LRegex) (w : list A) (start delta : nat),
    (forall d, d <= delta -> not_match_regex r1 w start d \/ not_match_regex r2 w (start + d) (delta - d))
    -> not_match_regex (Concat r1 r2) w start delta
| not_match_union : forall (r1 r2 : LRegex) (w : list A) (start d : nat),
    not_match_regex r1 w start d -> not_match_regex r2 w start d 
    -> not_match_regex (r1 ∪ r2) w start d
| not_match_star : forall (r : LRegex) (w : list A) (start delta : nat),
    (delta <> 0)
    -> (forall d, 0 < d <= delta -> not_match_regex r w start d \/ not_match_regex (r *) w (start + d) (delta - d))
    -> not_match_regex (r *) w start delta
| not_match_lookahead_length : forall (r : LRegex) (w : list A) (start delta : nat),
    (delta <> 0) -> not_match_regex ( (?> r) ) w start delta
| not_match_lookahead_false : forall (r : LRegex) (w : list A) (start delta : nat),
    not_match_regex r w start (length w - start) -> not_match_regex ( (?> r) ) w start delta
| not_match_lookbehind_length : forall (r : LRegex) (w : list A) (start delta : nat),
    (delta <> 0) -> not_match_regex ((?< r)) w start delta
| not_match_lookbehind_false : forall (r : LRegex) (w : list A) (start delta : nat),
    not_match_regex r w 0 start -> not_match_regex ((?< r)) w start delta
| not_match_neglookahead_length : forall (r : LRegex) (w : list A) (start delta : nat),
    (delta <> 0) -> not_match_regex ( (?!> r) ) w start delta
| not_match_neglookahead_false : forall (r : LRegex) (w : list A) (start delta : nat),
    match_regex r w start (length w - start) -> not_match_regex ( (?!> r) ) w start delta
| not_match_neglookbehind_length : forall (r : LRegex) (w : list A) (start delta : nat),
    (delta <> 0) -> not_match_regex ((?<! r)) w start delta
| not_match_neglookbehind_false : forall (r : LRegex) (w : list A) (start delta : nat),
    match_regex r w 0 start -> not_match_regex ((?<! r)) w start delta
.

Lemma match_eps_iff : forall w start delta,
    match_regex ε w start delta <-> delta = 0.
Proof.
    split; intros.
    - now inversion H.
    - subst. apply match_epsilon.
Qed.

Lemma not_match_eps_iff : forall w start delta,
    not_match_regex ε w start delta <-> delta <> 0.
Proof.
    split; intros.
    - now inversion H.
    - destruct delta.
      + tauto.
      + now apply not_match_epsilon.
Qed.

Lemma match_class_iff : forall pred w start delta,
    match_regex (CharClass pred) w start delta <-> 
    exists a, (pred a = true) /\ (nth_error w start = Some a) /\ (delta = 1).
Proof.
    split; intros.
    - inversion H. exists a. auto.
    - destruct H as [a [H1 [H2 H3]]]. subst delta. apply (match_class a); assumption.
Qed.

Lemma not_match_class_iff : forall pred w start delta,
    not_match_regex (CharClass pred) w start delta <-> 
            (delta <> 1) 
        \/  (nth_error w start = None)
        \/  (exists a, nth_error w start = Some a /\ pred a = false).
Proof.
    split; intros.
    - inversion H; firstorder.
    - firstorder.
      * now apply not_match_class_length.
      * now apply not_match_class_index.
      * now apply not_match_class_false with (a := x).
Qed.

Lemma match_union_iff : forall r1 r2 w start delta,
    match_regex (Union r1 r2) w start delta <-> 
    (match_regex r1 w start delta) \/ (match_regex r2 w start delta).
Proof.
    split; intros.
    - inversion H; auto.
    - destruct H.
      + now apply match_union_l.
      + now apply match_union_r.
Qed.

Lemma not_match_union_iff : forall r1 r2 w start delta,
    not_match_regex (Union r1 r2) w start delta <-> 
    (not_match_regex r1 w start delta) /\ (not_match_regex r2 w start delta).
Proof.
    split; intros.
    - inversion H; auto.
    - destruct H. apply not_match_union; assumption.
Qed.

Lemma match_concat_iff : forall r1 r2 w start delta,
    match_regex (Concat r1 r2) w start delta <-> 
        exists d1 d2, 
            (match_regex r1 w start d1) 
            /\ (match_regex r2 w (start + d1) d2)
            /\ (delta = d1 + d2).
Proof.
    split; intros.
    - inversion H. exists d1. exists d2. auto.
    - destruct H as [d1 [d2 [H1 [H2 H3]]]]. subst delta.
      now apply match_concat.
Qed.

Lemma match_concat_iff_2 : forall r1 r2 w start delta,
    match_regex (Concat r1 r2) w start delta <-> 
    exists d1, 
        (match_regex r1 w start d1) 
        /\ (match_regex r2 w (start + d1) (delta - d1))
        /\ d1 <= delta.
Proof.
    intros. rewrite match_concat_iff; 
        split; intros; 
        destruct H as [d1 [d2 [H1 H]]]; exists d1.
    + split. assumption.
      destruct H as [H2 H3].
      assert (d2 = delta - d1) as H4. lia.
      split.
        * now subst d2.
        * lia.
    + exists (delta - d1). repeat split; auto.
      lia.
Qed.

Lemma not_match_concat_iff : forall r1 r2 w start delta,
    not_match_regex (Concat r1 r2) w start delta <-> 
    forall d, d <= delta 
        -> not_match_regex r1 w start d 
        \/ not_match_regex r2 w (start + d) (delta - d).
Proof.
    split; intro.
    -  inversion H. auto.
    -  constructor. auto.
Qed.

Lemma match_lookahead_iff : forall r w start delta,
    match_regex (LookAhead r) w start delta <-> 
    (match_regex r w start (length w - start)) /\ (delta = 0).
Proof.
    split; intros.
    - inversion H. split. assumption. reflexivity.
    - destruct H as [H1 H2]. subst delta. apply match_lookahead. assumption.
Qed.

Lemma not_match_lookahead_iff : forall r w start delta,
    not_match_regex (LookAhead r) w start delta <-> 
    (not_match_regex r w start (length w - start)) \/ (delta <> 0).
Proof.
    split; intros.
    - inversion H. right. lia.
      auto.
    - assert (delta = 0 \/ delta <> 0) as Hd by lia. destruct Hd; destruct H.
      + now apply not_match_lookahead_false.
      + tauto.
      + now apply not_match_lookahead_length.
      + now apply not_match_lookahead_length. 
Qed.

Lemma match_neglookahead_iff : forall r w start delta,
    match_regex (NegLookAhead r) w start delta <-> 
    (not_match_regex r w start (length w - start)) /\ (delta = 0).
Proof.
    split; intros.
    - inversion H. split. assumption. reflexivity.
    - destruct H as [H1 H2]. subst delta. apply match_neglookahead. assumption.
Qed.

Lemma not_match_neglookahead_iff : forall r w start delta,
    not_match_regex (NegLookAhead r) w start delta <-> 
    (match_regex r w start (length w - start)) \/ (delta <> 0).
Proof.
    split; intros.
    - inversion H. right. lia.
      auto.
    - assert (delta = 0 \/ delta <> 0) as Hd by lia. destruct Hd; destruct H.
      + now apply not_match_neglookahead_false.
      + tauto.
      + now apply not_match_neglookahead_length.
      + now apply not_match_neglookahead_length.
Qed.

Lemma match_lookbehind_iff : forall r w start delta,
    match_regex (LookBehind r) w start delta <-> 
    (match_regex r w 0 start) /\ (delta = 0).
Proof.
    split; intros.
    - inversion H. split. assumption. reflexivity.
    - destruct H as [H1 H2]. subst delta. apply match_lookbehind. assumption.
Qed.

Lemma not_match_lookbehind_iff : forall r w start delta,
    not_match_regex (LookBehind r) w start delta <-> 
    (not_match_regex r w 0 start) \/ (delta <> 0).
Proof.
    split; intros.
    - inversion H. right. lia.
      auto.
    - assert (delta = 0 \/ delta <> 0) as Hd by lia. destruct Hd; destruct H.
      + now apply not_match_lookbehind_false.
      + tauto.
      + now apply not_match_lookbehind_length.
      + now apply not_match_lookbehind_length.
Qed.

Lemma match_neglookbehind_iff : forall r w start delta,
    match_regex (NegLookBehind r) w start delta <-> 
    (not_match_regex r w 0 start) /\ (delta = 0).
Proof.
    split; intros.
    - inversion H. split. assumption. reflexivity.
    - destruct H as [H1 H2]. subst delta. apply match_neglookbehind. assumption.
Qed.

Lemma not_match_neglookbehind_iff : forall r w start delta,
    not_match_regex (NegLookBehind r) w start delta <-> 
    (match_regex r w 0 start) \/ (delta <> 0).
Proof.
    split; intros.
    - inversion H. right. lia.
      auto.
    - assert (delta = 0 \/ delta <> 0) as Hd by lia. destruct Hd; destruct H.
      + now apply not_match_neglookbehind_false.
      + tauto.
      + now apply not_match_neglookbehind_length.
      + now apply not_match_neglookbehind_length.
Qed.

Lemma match_star_nonempty : forall r w start delta,
    match_regex (Star r) w start delta <->
        delta = 0 \/
        exists d1, 
            0 < d1 /\ d1 <= delta
            /\ (match_regex r w start d1) 
            /\ (match_regex (Star r) w (start + d1) (delta - d1)).
Proof.
    intros r w start delta.
    split.
    * intros. remember (Star r) as e.
      induction H; try discriminate.
      - tauto.
      - assert (r0 = r) by now inversion Heqe. subst r0.
        assert (d1 + d2 = 0 \/ d1 + d2 > 0) by lia.
        destruct H1; auto.
        apply IHmatch_regex2 in Heqe.
        destruct Heqe as [Heqe | Heqe].
        + subst d2. right. exists d1.
          repeat split; try lia; auto.
          replace (d1 + 0 - d1) with 0 by lia.
          auto.
        + destruct Heqe as [d3 [X1 [X2 [X3 X4]]]].
        right. assert (d1 = 0 \/ d1 > 0) as Hd by lia. destruct Hd.
        ** subst d1. exists d3.
           repeat split; auto.
           replace (start + 0) with start in X3 by lia.
           assumption.
           replace (start + 0 + d3) with (start + d3) in X4 by lia.
           assumption.
        ** exists d1.
           repeat split; auto.
           lia. replace (d1 + d2 - d1) with d2 by lia.
            assumption.
    * intros. destruct H as [H | H].
      - subst delta. constructor.
      - destruct H as [d1 [H1 [H2 [H3 H4]]]].
        replace delta with (d1 + (delta - d1)) by lia.
        apply match_star; assumption.
Qed.

Lemma match_star_iff : forall r w start delta,
    match_regex (Star r) w start delta <->
        delta = 0 \/
        exists d,
            d <= delta
            /\ (match_regex r w start d) 
            /\ (match_regex (Star r) w (start + d) (delta - d)).
Proof.
    split; intros.
    - inversion H.
      + auto.
      + right. exists d1.
        repeat split; auto. lia.
        now replace (d1 + d2 - d1) with d2 by lia.
    - destruct H as [H | H].
      + subst delta. constructor.
      + destruct H as [d [Hd [H1 H2]]].
        replace delta with (d + (delta - d)).
        apply match_star. auto. auto.
        lia.
Qed.     

Lemma not_match_star_iff : forall r w start delta,
    not_match_regex (Star r) w start delta <->
        delta <> 0 /\
        forall d, 
            0 < d <= delta 
            -> not_match_regex r w start d 
            \/ not_match_regex (Star r) w (start + d) (delta - d).
Proof.
    split; intros.
    - inversion H. auto.
    - apply not_match_star; tauto.
Qed.

Lemma bounded_lem (P : nat -> Prop) :
    (forall n, P n \/ ~ P n)
    -> forall N, (exists n, n <= N /\ P n) \/ ~ (exists n, n <= N /\ P n).
Proof.
    intro HP.
    induction N.
    - destruct (HP 0).
      + left. exists 0. auto.
      + right. intro. destruct H0 as [n [Hn HPn]].
        assert (n = 0) by lia. congruence.
    - destruct (HP (S N)).
      + left. exists (S N). auto.
      + destruct (IHN) as [[ n [IH1 IH2]] | IH ].
        * left. exists n. auto.
        * right. intro. destruct H0 as [m [Hm HPm]].
          assert (m = S N \/ m < S N) as Hm' by lia.
          destruct Hm'.
          ** subst m. contradiction.
          ** assert (m <= N) by lia. apply IH.
             exists m. auto.
Qed.

Lemma star_lem : forall r,
    (forall w start delta, 
        match_regex r w start delta \/ ~ match_regex r w start delta)
    -> forall w start delta,
        match_regex (Star r) w start delta \/ ~ match_regex (Star r) w start delta.
Proof.
    intros r Hrlem w start delta. revert start.
    induction delta using lt_wf_ind; intros.
    rewrite match_star_nonempty.
    (* get rid of the possibility that delta = 0 *)
    assert (delta = 0 \/ delta <> 0) as [Hd | Hd] by lia; [firstorder|].
    pose (P (d : nat) :=
        0 < d
        /\ match_regex r w start d
        /\ match_regex (Star r) w (start + d) (delta - d)).
    enough ((exists d, d <= delta /\ P d) \/ ~ (exists d, d <= delta /\ P d)) 
        by firstorder.
    apply bounded_lem.
    intros d. subst P. simpl.
    (* get rid of the case when d = 0 *)
    assert (d = 0 \/ d <> 0) as [Hd' | Hd'] by lia ; [lia|].
    assert (delta - d < delta) as Hdelta by lia.
    destruct (Hrlem w start d);
        destruct (H (delta - d) Hdelta (start + d)); firstorder.
    left. split. lia. split; auto.
Qed.

Lemma concat_lem : forall r1 r2,
    (forall w start delta, 
        match_regex r1 w start delta \/ ~ match_regex r1 w start delta)
    -> (forall w start delta, 
        match_regex r2 w start delta \/ ~ match_regex r2 w start delta)
    -> forall w start delta,
        match_regex (Concat r1 r2) w start delta 
        \/ ~ match_regex (Concat r1 r2) w start delta.
Proof.
    intros r1 r2 IH1 IH2.
    intros w start delta.
    rewrite match_concat_iff_2.
    pose (P (d : nat) := match_regex r1 w start d /\ match_regex r2 w (start + d) (delta - d)).
    enough ((exists d, d <= delta /\ P d) \/ ~ (exists d, d <= delta /\ P d)) by firstorder.
    apply bounded_lem. subst P. simpl.
    intro d.
    destruct (IH1 w start d);
     destruct (IH2 w (start + d) (delta - d));
      firstorder.
Qed.

Lemma star_match_not_match : forall r,
    (forall w start delta,
        ~ (match_regex r w start delta) <-> not_match_regex r w start delta)
    -> (forall w start delta,
        match_regex r w start delta \/ ~ match_regex r w start delta)
    -> forall w start delta,
        ~ (match_regex (Star r) w start delta) 
        <-> not_match_regex (Star r) w start delta.
Proof.
    intros r Hr Hlem w start delta. revert start.
    induction delta using lt_wf_ind; intros.
    rewrite match_star_nonempty, not_match_star_iff.
    assert (delta = 0 \/ delta <> 0) as [Hd | Hd] by lia; [firstorder|].
    split; intro.
    - split; auto.
      intros dd Hdd.
      rewrite <- Hr. rewrite <- H by lia.
      destruct (Hlem w start dd);
        destruct (star_lem r Hlem w (start + dd) (delta - dd));
            firstorder.
    - intro. destruct H1; auto.
      firstorder. specialize (H2 x).
      rewrite <- Hr in H2. rewrite <- H in H2 by lia.
      firstorder.
Qed.

Lemma match_iff_not_match_aux : forall r w start delta,
    (~ (match_regex r w start delta) 
        <-> (not_match_regex r w start delta))
    /\ (match_regex r w start delta 
        \/ ~ (match_regex r w start delta)).
Proof.
    induction r; intros.
    { (* eps *)
        rewrite match_eps_iff.
        rewrite not_match_eps_iff.
        lia.
    }
    { (* charclass *)
        rewrite match_class_iff.
        rewrite not_match_class_iff.
        split.
        {  split; intro.
        - assert (delta = 1 \/ delta <> 1) as Hd by lia. 
          destruct Hd; auto.
          subst delta.
          destruct (nth_error).
          + right. right. exists a. split; auto.
            destruct (b a) eqn:F; auto.
            contradiction H. exists a; auto.
          + auto.
        - destruct H as [H | [H | H]]; 
            intro; firstorder; congruence.
        }
        { assert (delta = 1 \/ delta <> 1) as Hd by lia.
          destruct (nth_error w start) as [a | ]eqn:E;
           destruct Hd; 
            try destruct (b a) eqn:F;
            firstorder.
         - right. intro. destruct H0. firstorder. congruence.
         - right. intro. destruct H0. firstorder. discriminate. 
        }
    }
    { (* concat *)
        rewrite match_concat_iff.
        rewrite not_match_concat_iff.
        assert 
            (forall w start delta, (~ match_regex r1 w start delta <-> not_match_regex r1 w start delta))
        as IH1a by firstorder.
        assert 
            (forall w start delta, (~ match_regex r2 w start delta <-> not_match_regex r2 w start delta))
        as IH2a by firstorder.
        assert
            (forall w start delta, (match_regex r1 w start delta \/ ~ match_regex r1 w start delta))
        as IH1b by firstorder.
        assert
            (forall w start delta, (match_regex r2 w start delta \/ ~ match_regex r2 w start delta))
        as IH2b by firstorder.
        clear IHr1 IHr2.
        split.
        {  split; intro.
        - intros.
        rewrite <- IH1a.
        rewrite <- IH2a.
        destruct (IH1b w start d) as [H1 | H1];
        destruct (IH2b w (start + d) (delta - d)) as [H2 | H2]; auto.
        exfalso. apply H. exists d, (delta - d). repeat split; auto. lia.
        - intros [d [dd [Hd [Hdd Hdelta]]]].
          exfalso. assert (d <= delta) by lia.
          apply H in H0. 
          rewrite <- IH1a in H0.
          rewrite <- IH2a in H0. firstorder. 
          replace dd with (delta - d) in * by lia. auto.
        }
        { rewrite <- match_concat_iff. rewrite match_concat_iff_2.
          pose (P (d : nat) := match_regex r1 w start d /\ match_regex r2 w (start + d) (delta - d)).
          enough ((exists d, d <= delta /\ P d) \/ ~ (exists d, d <= delta /\ P d)) by firstorder.
          apply bounded_lem. subst P. simpl.
          intro d. destruct (IH1b w start d); destruct (IH2b w (start + d) (delta - d)); firstorder.
        }
    }
    { (* union *)
       rewrite match_union_iff.
       rewrite not_match_union_iff.
       firstorder. 
       destruct (IHr1 w start delta); destruct (IHr2 w start delta); firstorder.
    }
    { (* star *)
      split.
      { apply star_match_not_match; firstorder. }
      { apply star_lem; firstorder. }
    }
    { (* lookahead *)
        rewrite match_lookahead_iff.
        rewrite not_match_lookahead_iff.
        assert (delta = 0 \/ delta <> 0) as [Hd | Hd] by lia; firstorder.
    }
    {   (* lookbehind *)
        rewrite match_lookbehind_iff.
        rewrite not_match_lookbehind_iff.
        assert (delta = 0 \/ delta <> 0) as [Hd | Hd] by lia; firstorder.
    }
    {   (* neg-lookahead *)
        rewrite match_neglookahead_iff.
        rewrite not_match_neglookahead_iff.
        assert (delta = 0 \/ delta <> 0) as [Hd | Hd] by lia; firstorder.
    }
    {   (* neg-lookbehind *)
        rewrite match_neglookbehind_iff.
        rewrite not_match_neglookbehind_iff.
        assert (delta = 0 \/ delta <> 0) as [Hd | Hd] by lia; firstorder.
    }
Qed.


Lemma match_not_match : forall r w start delta,
    ~ (match_regex r w start delta) <-> (not_match_regex r w start delta).
Proof.
    intros. 
    pose proof match_iff_not_match_aux r w start delta.
    firstorder.
Qed.

Lemma match_lem : forall r w start delta,
    match_regex r w start delta \/ ~ (match_regex r w start delta).
Proof.
    intros. 
    pose proof match_iff_not_match_aux r w start delta.
    firstorder.
Qed.

Definition is_tape (r : LRegex) (w : list A) (t : list bool) : Prop :=
    (length t = length w + 1) /\
    forall delta,
        delta <= length w ->
        (nth_error t delta = Some true <-> match_regex r w 0 delta) /\
        (nth_error t delta = Some false <-> ~ match_regex r w 0 delta).

Definition is_tape_slice (r : LRegex) (w : list A) (t : list bool) (start delta : nat) : Prop :=
    start + delta <= length w /\
    (length t = delta + 1) /\
    forall i,
        i <= delta ->
        (nth_error t i = Some true <-> match_regex r w start i) /\
        (nth_error t i = Some false <-> ~ match_regex r w start i).

Definition is_scanMatcher (scanMatch : LRegex -> list A -> list bool) : Prop :=
    forall r w,
        is_tape r w (scanMatch r w).

Lemma tape_length : forall r w t,
    is_tape r w t
    -> length t = length w + 1.
Proof.
    firstorder.
Qed.
                
Lemma scanMatcher_length : forall scanMatch,
    is_scanMatcher scanMatch
    -> forall r w,
        length (scanMatch r w) = length w + 1.
Proof.
    firstorder.
Qed.

Lemma tape_none : forall r w t,
    is_tape r w t
    -> forall delta,
        delta > length w
        <-> nth_error t delta = None.
Proof.
    intros. unfold is_tape in H.
    destruct H as [Hlen H].
    specialize (H delta).
    split; intro.
    - rewrite nth_error_None. lia.
    - rewrite nth_error_None in H0. lia.
Qed.

Lemma scanMatcher_none : forall scanMatch,
    is_scanMatcher scanMatch
    -> forall r w delta,
        delta > length w
        <-> nth_error (scanMatch r w) delta = None.
Proof.
    intros. unfold is_scanMatcher in H.
    specialize (H r w).
    apply tape_none with (delta := delta) in H.
    firstorder.
Qed.        

End Semantics.

Hint Constructors match_regex : regex.
Hint Resolve match_eps_iff : regex.
Hint Resolve match_class_iff : regex.
Hint Resolve match_union_iff : regex.
Hint Resolve match_concat_iff match_concat_iff_2 : regex.
Hint Resolve match_lookahead_iff : regex.
Hint Resolve match_neglookahead_iff : regex.
Hint Resolve match_lookbehind_iff : regex.
Hint Resolve match_neglookbehind_iff : regex.
Hint Resolve match_star_iff match_star_nonempty : regex.
Hint Resolve match_lem : regex.
Hint Resolve scanMatcher_none : regex.