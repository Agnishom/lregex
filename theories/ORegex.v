(**

This file contains a number of important notions involving Regular Expressions with Oracle Queries (ORegex).

  1. The notion of [ostring : Type] formalizes the notion of a string annotated with oracle valuations. An [ostring] is a list over [A] along with a list of [valuation] (i.e, list of [boolean])
    - The predicate [ostring_wf] is a predicate that asserts that an [ostring] is well-formed.
    - The [olength : ostring -> nat] function is the analogue of [length] for [ostring].
    - [ostring] should be cleaved via the functions [ofirstn : nat -> ostring -> ostring] and [oskipn : nat -> ostring -> ostring].
    - The [orev : ostring -> ostring] function is the analogue of [rev] for [ostring].
    - This file contains many lemmas connecting [olength], [orev], [ofirstn], and [oskipn] to each other.

  2. The type [ORegex] denotes Regular Expressions with Oracle Queries. The predicate [match_oregex : ORegex -> ostring -> Prop] is used to certify that an [ORegex] matches a given [ostring].

*)

Require Import Lia.
Require Import Coq.Lists.List.


Import ListNotations.

Require Import ListLemmas.

Section OString.

Generalizable Variables A.
Variable (A : Type).

Definition valuation : Type := list bool.
Definition ostring : Type := (list A) * (list valuation).

Definition outer_length_wf (s : ostring) : Prop :=
  length (fst s) + 1 = length (snd s).
Definition inner_length_wf (s : ostring) : Prop :=
  forall u v : valuation,
    In u (snd s) -> In v (snd s) -> length u = length v.
Definition ostring_wf (s : ostring) : Prop :=
  outer_length_wf s /\ inner_length_wf s.

Definition olength (s : ostring) : nat := length (fst s).
Definition ofirstn (n : nat) (s : ostring) : ostring :=
  (firstn n (fst s), firstn (S n) (snd s)).
Definition oskipn (n : nat) (s : ostring) : ostring :=
  (skipn n (fst s), 
    skipn (Nat.min n (length (fst s))) (snd s)).
Definition orev (s : ostring) : ostring :=
  (rev (fst s), rev (snd s)).

Lemma ofirstn_outer_length_wf : forall n s,
  outer_length_wf s -> outer_length_wf (ofirstn n s).
Proof.
    unfold outer_length_wf, ofirstn.
    destruct s as (o, w). 
    simpl fst. simpl snd.
    rewrite firstn_length. intros.
    destruct w eqn:Hw.
    - simpl in *. lia. 
    - simpl in *.
      enough (Nat.min n (length o) = length (firstn n l)) by lia.
      rewrite firstn_length. lia.
Qed.

Lemma ofirstn_inner_length_wf : forall n s,
  inner_length_wf s -> inner_length_wf (ofirstn n s).
Proof.
    unfold inner_length_wf, ofirstn.
    destruct s as (o, w). 
    simpl fst. simpl snd at 1 2 4 6.
    remember (S n) as n'. simpl snd.
    subst n'. intros.
    apply H; 
      rewrite <- firstn_skipn with (n := (S n));
      rewrite in_app_iff; auto.
Qed.

Lemma ofirstn_ostring_wf : forall n s,
  ostring_wf s -> ostring_wf (ofirstn n s).
Proof.
    firstorder using ofirstn_outer_length_wf, ofirstn_inner_length_wf.
Qed.

Lemma oskipn_outer_length_wf : forall n s,
  outer_length_wf s -> outer_length_wf (oskipn n s).
Proof.
    unfold outer_length_wf, oskipn.
    destruct s as (o, w). 
    simpl fst. simpl snd.
    repeat rewrite skipn_length. 
    intros. lia.
Qed.

Lemma oskipn_inner_length_wf : forall n s,
  inner_length_wf s -> inner_length_wf (oskipn n s).
Proof.
    unfold inner_length_wf, oskipn.
    destruct s as (o, w). 
    simpl fst. simpl snd.
    intros.
    apply H; 
      rewrite <- firstn_skipn with (n := Nat.min n (length o));
      rewrite in_app_iff; auto.
Qed.

Lemma oskipn_ostring_wf : forall n s,
  ostring_wf s -> ostring_wf (oskipn n s).
Proof.
    firstorder using oskipn_outer_length_wf, oskipn_inner_length_wf.
Qed.

Lemma orev_outer_length_wf : forall s,
  outer_length_wf s -> outer_length_wf (orev s).
Proof.
    unfold outer_length_wf, orev.
    destruct s as (o, w). 
    simpl. 
    repeat rewrite rev_length.
    lia.
Qed.

Lemma orev_inner_length_wf : forall s,
  inner_length_wf s -> inner_length_wf (orev s).
Proof.
  unfold inner_length_wf, orev.
  destruct s as (o, w). 
  simpl. intros.  
  rewrite <- in_rev in *.
  auto.
Qed.

Lemma orev_ostring_wf : forall s,
  ostring_wf s -> ostring_wf (orev s).
Proof.
    firstorder using orev_outer_length_wf, orev_inner_length_wf.
Qed.

Lemma orev_involutive : forall s,
   orev (orev s) = s.
Proof.
  unfold orev.
  destruct s as (o, w). simpl.
  intros. f_equal; apply rev_involutive.
Qed.

Lemma orev_olength : forall s,
  olength (orev s) = olength s.
Proof.
  unfold olength, orev.
  destruct s as (o, w). simpl.
  apply rev_length.
Qed.

Lemma ofirstn_olength : forall n s,
  olength (ofirstn n s) = min n (olength s).
Proof.
  unfold olength, ofirstn.
  destruct s as (o, w). simpl.
  rewrite firstn_length. lia.
Qed.

Lemma oskipn_olength : forall n s,
  olength (oskipn n s) = (olength s - n).
Proof.
  unfold olength, oskipn.
  destruct s as (o, w). simpl.
  rewrite skipn_length. lia.
Qed.


Lemma ofirstn_oskipn_orev : forall n ostr,
  outer_length_wf ostr
  -> ofirstn n ostr = orev (oskipn (olength ostr - n) (orev ostr)).
Proof.
  unfold outer_length_wf.
  unfold ofirstn, oskipn, orev.
  destruct ostr as (o, w). 
  simpl fst. simpl snd. intro.
  f_equal. 
  - unfold olength. simpl.
    apply firstn_skipn_rev.
  - unfold olength. simpl fst.
    rewrite rev_length.
    assert (length o >= n \/ length o < n) by lia.
    destruct H0.
    + replace (min (length o - n) (length o)) with (length o - n) by lia.
      replace (length o - n) with (length w - (S n)) by lia.
      apply firstn_skipn_rev.
    + replace (min (length o - n) (length o)) with 0 by lia.
      simpl skipn. rewrite rev_involutive.
      now rewrite firstn_all2 by lia.
Qed.

Lemma ofirstn_orev : forall n ostr,
  outer_length_wf ostr
  -> ofirstn n (orev ostr) = orev (oskipn (olength ostr - n) ostr).
Proof.
  unfold outer_length_wf.
  unfold ofirstn, oskipn, orev.
  destruct ostr as (o, w).
  simpl fst. simpl snd. intro.
  f_equal.
  - unfold olength. simpl.
    apply firstn_rev.
  - unfold olength. simpl fst.
    assert (length o >= n \/ length o < n) by lia.
    destruct H0.
    + replace (min (length o - n) (length o)) with (length o - n) by lia.
      replace (length o - n) with (length w - (S n)) by lia.
      apply firstn_rev.
    + replace (min (length o - n) (length o)) with 0 by lia.
      simpl skipn.
      rewrite firstn_all2. auto.
      rewrite rev_length. lia.
Qed.

Lemma oskipn_orev : forall n ostr,
  outer_length_wf ostr
  -> oskipn n (orev ostr) = orev (ofirstn (olength ostr - n) ostr).
Proof.
  unfold outer_length_wf.
  unfold ofirstn, oskipn, orev.
  destruct ostr as (o, w).
  simpl fst. simpl snd at 1 2 5.
  unfold olength. simpl fst.
  remember (S (length o - n)) as m.
  simpl snd. subst. intro.
  f_equal.
  - apply skipn_rev.
  - rewrite rev_length. 
    assert (length o >= n \/ length o < n) by lia.
    destruct H0.
    + replace (min n (length o)) with n by lia.
      replace (S (length o - n)) with (length w - n) by lia.
      apply skipn_rev.
    + replace (min n (length o)) with (length o) by lia.
      replace (S (length o - n)) with (length w - length o) by lia.
      apply skipn_rev.
Qed.

Lemma ofirstn_all2 : forall n ostr,
  outer_length_wf ostr ->
  olength ostr <= n -> ofirstn n ostr = ostr.
Proof.
  unfold ofirstn, olength, outer_length_wf.
  destruct ostr as (w, o).
  simpl fst. simpl snd.
  intros.
  now repeat rewrite firstn_all2 by lia.
Qed.

Lemma ofirstn_all3 : forall n ostr,
  outer_length_wf ostr ->
  olength ostr <= n -> ofirstn n ostr = ofirstn (olength ostr) ostr.
Proof.
  intros. repeat rewrite ofirstn_all2; auto.
Qed.

Lemma oskipn_all2 : forall n ostr,
  outer_length_wf ostr ->
  olength ostr <= n -> oskipn n ostr = (nil, skipn (olength ostr) (snd ostr)).
Proof.
  unfold outer_length_wf, oskipn, olength.
  destruct ostr as (w, o).
  simpl fst. simpl snd.
  intros.
  f_equal.
  - now rewrite skipn_all2.
  - f_equal. lia.
Qed.

Lemma oskipn_all3 : forall n ostr,
  outer_length_wf ostr ->
  olength ostr <= n -> oskipn n ostr = oskipn (olength ostr) ostr.
Proof.
  intros. repeat rewrite oskipn_all2; auto.
Qed.

Lemma oskipn0 : forall ostr,
  oskipn 0 ostr = ostr.
Proof.
  unfold oskipn.
  destruct ostr as (w, o).
  simpl fst. simpl snd.
  replace (min 0 (length w)) with 0 by lia.
  auto.
Qed.

Lemma ofirstn_ofirstn : forall n m ostr,
  ofirstn n (ofirstn m ostr) = ofirstn (min n m) ostr.
Proof.
  unfold ofirstn.
  destruct ostr as (w, o).
  simpl fst. simpl snd at 2 3.
  f_equal.
  - apply firstn_firstn.
  - remember (S m) as m'.
    simpl snd. rewrite firstn_firstn. f_equal.
    lia.
Qed.


Lemma oskipn_oskipn : forall n m ostr,
  oskipn n (oskipn m ostr) = oskipn (n + m) ostr.
Proof.
  unfold oskipn.
  destruct ostr as (w, o).
  simpl fst. simpl snd at 2 3.
  f_equal.
  - apply skipn_skipn.
  - remember (S m) as m'.
    simpl snd. rewrite skipn_skipn.
    rewrite skipn_length. f_equal.
    lia.
Qed.


Lemma oskipn_ofirstn_comm : forall n m ostr,
  outer_length_wf ostr ->
  m <= n ->
  oskipn m (ofirstn n ostr) = ofirstn (n - m) (oskipn m ostr).
Proof.
  unfold oskipn, ofirstn.
  destruct ostr as (w, o).
  unfold outer_length_wf.
  simpl fst. remember (S n) as n'. simpl snd.
  intros Hwf Hmn.
  f_equal.
  - apply skipn_firstn_comm.
  - rewrite skipn_firstn_comm.
    rewrite firstn_length.
    assert (length w < m \/ length w >= m) as Hm by lia.
    assert (length w < n \/ length w >= n) as Hn by lia.
    destruct Hm, Hn.
    { replace (min n (length w)) with (length w) by lia. 
      replace (min m (length w)) with (length w) by lia.
      repeat rewrite firstn_all2. auto.
      - rewrite skipn_length. lia.
      - rewrite skipn_length. lia.
    }
    { replace (min m (length w)) with (length w) by lia.
      replace (min n (length w)) with n by lia.
      replace (min m n) with m by lia.
      subst n'. replace (S n - m) with (S (n - m)) by lia.
      f_equal.
      repeat rewrite skipn_all2 by lia.
      auto.
    }
    { replace (min n (length w)) with (length w) by lia.
      replace (min m (length w)) with m by lia.
      f_equal. lia.
    }
    { replace (min n (length w)) with n by lia.
      replace (min m (length w)) with m by lia.
      replace (min m n) with m by lia.
      f_equal. lia.
    }
Qed.

Definition ofirstval (os : ostring) : option valuation :=
  hd_error (snd os).

Lemma ofirstval_Some (os : ostring) :
  outer_length_wf os -> exists v0, ofirstval os = Some v0.
Proof.
  unfold outer_length_wf, ofirstval.
  destruct os as (w, o).
  simpl. intros Hwf.
  destruct o as [| v0 o].
  - simpl in Hwf. lia.
  - exists v0. auto.
Qed.

Definition olastval (os : ostring) : option valuation :=
  last_error (snd os).

Lemma olastval_Some (os : ostring) :
  outer_length_wf os -> exists v0, olastval os = Some v0.
Proof.
  unfold outer_length_wf, olastval.
  destruct os as (w, o).
  simpl.
  destruct (unsnoc o) as [[l x] | ] eqn:E.
  - rewrite unsnoc_Some in E.
    subst. exists x.
    rewrite last_error_Some.
    eauto.
  - rewrite unsnoc_None in E.
    subst. simpl. lia.
Qed.

Lemma ostring_ind (P : ostring -> Prop) :
  (forall v0, P ([], [v0])) ->
  (forall v0 a0 w o, outer_length_wf (w, o) -> P (w, o) -> P (a0 :: w, v0 :: o)) ->
  forall os, outer_length_wf os -> P os.
Proof.
  intros Hbase Hstep.
  destruct os as (w, o).
  revert o. induction w as [| a0 w IHw]; intros o Hwf.
  - unfold outer_length_wf in Hwf. simpl in Hwf.
    destruct o as [| v0 o]. { simpl in Hwf. lia. }
    destruct o as [| v1 o]. 2: { simpl in Hwf. lia. }
    apply Hbase.
  - unfold outer_length_wf in Hwf. simpl in Hwf.
    destruct o as [| v0 o]. { simpl in Hwf. lia. }
    apply Hstep. 
    + unfold outer_length_wf. simpl. 
    simpl in Hwf. lia.
    + apply IHw. unfold outer_length_wf in *. simpl in *. lia. 
Qed.

Lemma ostring_rev_ind (P : ostring -> Prop) :
  (forall v0, P ([], [v0])) ->
  (forall v a w o, outer_length_wf (w, o) -> P (w, o) -> P (w ++ [a], o ++ [v])) ->
  forall os, outer_length_wf os -> P os.
Proof.
  intros Hbase Hstep.
  destruct os as (w, o).
  revert o. induction w as [| a w IHw] using rev_ind.
  - intros o Hwf. unfold outer_length_wf in Hwf. simpl in Hwf.
    destruct o as [| v0 o]. { simpl in Hwf. lia. }
    destruct o as [| v1 o]. 2: { simpl in Hwf. lia. }
    apply Hbase.
  - intros o Hwf. unfold outer_length_wf in Hwf. simpl in Hwf.
    destruct (unsnoc o) as [[o' ox] | ] eqn:E.
    2 : { rewrite unsnoc_None in E. subst. simpl in Hwf. lia. }
    rewrite unsnoc_Some in E. subst.
    apply Hstep.
    + unfold outer_length_wf. simpl.
    repeat rewrite app_length in Hwf. simpl in Hwf. lia.
    + apply IHw.
    unfold outer_length_wf. simpl.
    repeat rewrite app_length in Hwf. simpl in Hwf. lia.
Qed.

  
Inductive ORegex : Type :=
| OEpsilon : ORegex
| OCharClass : (A -> bool) -> ORegex
| OConcat : ORegex -> ORegex -> ORegex
| OUnion : ORegex -> ORegex -> ORegex
| OStar : ORegex -> ORegex
| OQueryPos : nat -> ORegex
| OQueryNeg : nat -> ORegex
.

Inductive match_oregex : ORegex -> ostring -> Prop :=
| omatch_epsilon : 
  forall (os : ostring), olength os = 0 -> match_oregex OEpsilon os
| omatch_charclass :
  forall (os : ostring) (a : A) (pred : A -> bool),
    olength os = 1 -> (hd_error (fst os)) = Some a -> pred a = true -> match_oregex (OCharClass pred) os
| omatch_concat :
   forall (r1 r2 : ORegex) (os : ostring) (n : nat),
     match_oregex r1 (ofirstn n os) -> match_oregex r2 (oskipn n os) -> match_oregex (OConcat r1 r2) os
| omatch_union_l :
    forall (r1 r2 : ORegex) (os : ostring),
      match_oregex r1 os -> match_oregex (OUnion r1 r2) os
| omatch_union_r :
    forall (r1 r2 : ORegex) (os : ostring),
      match_oregex r2 os -> match_oregex (OUnion r1 r2) os
| omatch_star_eps :
    forall (r : ORegex) (os : ostring),
      olength os = 0 -> match_oregex (OStar r) os
| omatch_star :
    forall (r : ORegex) (os : ostring) (n : nat),
      match_oregex r (ofirstn n os) -> match_oregex (OStar r) (oskipn n os) -> match_oregex (OStar r) os
| omatch_query_pos :
    forall (os : ostring) (v : valuation) (q : nat),
      olength os = 0 -> hd_error (snd os) = Some v -> nth_error v q = Some true -> match_oregex (OQueryPos q) os
| omatch_query_neg :
    forall (os : ostring) (v : valuation) (q : nat),
      olength os = 0 -> hd_error (snd os) = Some v -> nth_error v q = Some false -> match_oregex (OQueryNeg q) os
.

Lemma omatch_charclass_iff : forall (os : ostring) (pred : A -> bool),
  match_oregex (OCharClass pred) os 
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
  now apply omatch_charclass with (pred := pred) (a := a).
Qed.

Lemma omatch_union_iff : forall r1 r2 os,
  match_oregex (OUnion r1 r2) os 
  <-> match_oregex r1 os \/ match_oregex r2 os.
Proof.
  intros.
  split; intros.
  - inversion H; subst; auto.
  - destruct H; [apply omatch_union_l | apply omatch_union_r]; auto.
Qed.  

Lemma omatch_concat_iff : forall r1 r2 os,
  outer_length_wf os ->
  match_oregex (OConcat r1 r2) os 
  <-> exists n, 0 <= n <= olength os /\
    match_oregex r1 (ofirstn n os) /\ match_oregex r2 (oskipn n os).
Proof.
  intros r1 r2 os.
  split.
  - intros Hr12. inversion Hr12; subst.
    assert (n <= olength os \/ n > olength os) as [Hn | Hn] by lia.
    + exists n. repeat split; auto. lia.
    + exists (olength os). repeat split.
      lia. lia. 
      destruct os as (w, o).
      unfold olength in *. simpl in *.
      * rewrite ofirstn_all2 by auto.
        rewrite ofirstn_all2 in H2. auto.
        auto. unfold olength. simpl. lia.
      * rewrite oskipn_all2 by auto.
        rewrite oskipn_all2 in H4. auto.
        auto. unfold olength in *.
        destruct os as (w, o); simpl in *; lia.
  - intros [n [Hn [Hr1 Hr2]]].
    apply omatch_concat with n; auto.
Qed.


Lemma omatch_star_nonempty : forall r os,
  outer_length_wf os ->
  match_oregex (OStar r) os 
  <-> olength os = 0 
    \/ exists n,
      0 < n /\ n <= olength os /\
      match_oregex r (ofirstn n os) /\ match_oregex (OStar r) (oskipn n os).
Proof.
  intros r os Hwf.
  split.
  - intros H. remember (OStar r) as e.
    induction H; try discriminate.
    + tauto.
    + assert (r0 = r) by now inversion Heqe. subst r0.
      apply IHmatch_oregex2 in Heqe.
      clear IHmatch_oregex2. clear IHmatch_oregex1.
      assert (olength os = 0 \/ olength os > 0) as Hos by lia.
      destruct Hos; [tauto |].
      assert (n > olength os \/ n <= olength os) as Hn1 by lia.
      destruct Hn1.
      { 
        rewrite oskipn_all3 in H0.
        rewrite ofirstn_all3 in H.
        right. exists (olength os). repeat split.
        - lia.
        - lia.
        - assumption.
        - assumption.
        - assumption.
        - lia.
        - assumption.
        - lia.       
      }
      assert (n > 0 \/ n = 0) as Hn by lia. destruct Hn.
      {
        right. exists n. repeat split.
        - lia.
        - lia.
        - assumption.   
        - assumption.  
      }
      subst n. rewrite oskipn0 in *.
      destruct Heqe; tauto.
      now apply oskipn_outer_length_wf. 
  - intros H.
    destruct H as [H | [n [Hn [Hn' [Hr Hstar]]]]].
    + apply omatch_star_eps; assumption.
    + apply omatch_star with (n := n); assumption.
Qed.

Lemma ounmatch_star_r (r : ORegex) (os : ostring) :
  outer_length_wf os ->
  match_oregex (OStar r) os
  -> olength os = 0
    \/ exists n, match_oregex (OStar r) (ofirstn n os) 
       /\ match_oregex r (oskipn n os).
Proof.
  intros Hwf H.
  remember (OStar r) as e.
  induction H; inversion Heqe.
  - auto.
  - subst. right.
    pose proof (oskipn_outer_length_wf n os Hwf).
    pose proof (IHmatch_oregex2 H1 Heqe).
    clear IHmatch_oregex2. clear IHmatch_oregex1.
    clear Heqe. rename H2 into IH.
    destruct IH as [IH | [n' [IH1 IH2]]].
    + exists 0. split.
      * apply omatch_star_eps.
        rewrite ofirstn_olength. lia.
      * enough (oskipn 0 os = ofirstn n os).
        -- rewrite -> H2. assumption.
        -- rewrite oskipn0. rewrite ofirstn_all2. auto. auto.
           rewrite oskipn_olength in IH. lia.
    + exists (n' + n). split.
      * apply omatch_star with (n := n).
        -- rewrite ofirstn_ofirstn.
           replace (min n (n' + n)) with n by lia.
           assumption.
        -- rewrite oskipn_ofirstn_comm.
           replace (n' + n - n) with n' by lia.
           assumption.
           assumption. lia.
      * rewrite <- oskipn_oskipn. assumption.
Qed.  


Lemma omatch_star_r : forall r os n,
  outer_length_wf os ->
    match_oregex (OStar r) (ofirstn n os) 
    -> match_oregex r (oskipn n os) 
    -> match_oregex (OStar r) os.
Proof.
  assert (
    forall e os1,
      match_oregex e os1
      -> forall r os2,
      match_oregex r os2
      -> e = OStar r
      -> forall n os,
        outer_length_wf os
        -> n <= olength os
        -> os1 = ofirstn n os
        -> os2 = oskipn n os
        -> match_oregex e os
  ).
  { intros e os1 Hos1.
    induction Hos1; try (intros; discriminate).
    - intros. subst.
      rewrite ofirstn_olength in H.
      replace (min n (olength os0)) with n in H by lia.
      subst. rewrite oskipn0 in H0.
      apply omatch_star with (n := olength os0).
      + rewrite ofirstn_all2.
        inversion H1. subst. assumption. auto.
        auto.
      + rewrite oskipn_all2.
        apply omatch_star_eps. auto.
        auto. auto.
    - rename os into osA. rename n into nA.
      rename Hos1_1 into HosA1. rename Hos1_2 into HosA2.
      clear IHHos1_1. rename IHHos1_2 into IH.
      intros r' osB HosB Heq n os Hwf Hn HeqA HeqB.
      subst.
      specialize (IH r' (oskipn n os) HosB Heq (n - nA) (oskipn nA os)).
      specialize (IH (oskipn_outer_length_wf nA os Hwf)).
      rewrite oskipn_olength in IH.
      specialize (IH ltac:(lia)).
      pose proof (oskipn_ofirstn_comm n nA os Hwf).
      assert (nA > n \/ nA <= n) as HnA by lia.
      destruct HnA.
      { rewrite ofirstn_ofirstn in HosA1.
        replace (min nA n) with n in HosA1.
        inversion Heq. subst.
        apply omatch_star with (n := n).
        assumption. apply omatch_star with (n := olength (oskipn n os)).
        rewrite ofirstn_all2. assumption.
        apply oskipn_outer_length_wf. assumption.
        auto. rewrite oskipn_all2.
        apply omatch_star_eps. auto.
        apply oskipn_outer_length_wf. assumption.
        lia. lia.
      }
    specialize (H H0).
    specialize (IH H).
    rewrite oskipn_oskipn in IH.
    replace (n - nA + nA) with n in IH by lia.
    specialize (IH ltac:(reflexivity)).
    rewrite ofirstn_ofirstn in HosA1.
    replace (min nA n) with nA in HosA1 by lia.
    apply omatch_star with (n := nA); assumption.
  }
  intros.
  assert (n > olength os \/ n <= olength os) as Hn by lia.
  destruct Hn.
  { rewrite ofirstn_all2 in H1.
    auto. auto. lia. 
  }
  apply H with (os1 := ofirstn n os) (os2 := oskipn n os) 
    (r := r) (n := n); auto.
Qed. 

Definition oWildCard : ORegex :=
  OStar (OCharClass (fun _ => true)).

Lemma oWildCard_match (os : ostring) (Hwf : outer_length_wf os) :
  match_oregex oWildCard os.
Proof.
  revert Hwf.
  destruct os as (w, o).
  revert o.
  induction w. {
    (* when w is [] *)
    intros.
    now apply omatch_star_eps.
  }
  intros.
  destruct o as [ | o0 o']. { 
    unfold outer_length_wf in Hwf.
    simpl in Hwf. lia.
  }
  destruct o' as [ | o1 o'']. { 
    unfold outer_length_wf in Hwf.
    simpl in Hwf. lia.
  }
  apply omatch_star with (n := 1).
  - unfold ofirstn. simpl.
    eapply omatch_charclass; auto.
    simpl. reflexivity.
  - unfold oskipn. simpl.
    apply IHw.
    unfold outer_length_wf in Hwf |- *.
    simpl in Hwf |- *.
    lia.
Qed.

Definition rPass (or : ORegex) : ORegex :=
  OConcat oWildCard or.

Lemma rPass_match (or : ORegex) (os : ostring) (Hwf : outer_length_wf os): 
  match_oregex (rPass or) os
  <-> exists start, start <= olength os /\ match_oregex or (oskipn start os).
Proof.
  unfold rPass.
  rewrite omatch_concat_iff; [ | assumption].
  split; intros.
  - destruct H as [n [Hn [_ Hr]]].
    exists n. tauto.
  - destruct H as [n [Hn Hr]].
    exists n. repeat split.
    + lia.
    + assumption.
    + apply oWildCard_match. apply ofirstn_outer_length_wf. assumption.
    + assumption.
Qed.

End OString.

Arguments ORegex {A}.
Arguments OEpsilon {A}.
Arguments OCharClass {A}.
Arguments OConcat {A}.
Arguments OUnion {A}.
Arguments OStar {A}.
Arguments OQueryPos {A}.
Arguments OQueryNeg {A}.
Arguments ostring {A}.
Arguments olength {A}.
Arguments orev {A}.
Arguments ofirstn {A}.
Arguments oskipn {A}.
Arguments ofirstval {A}.
Arguments olastval {A}.
Arguments match_oregex {A}.
Arguments outer_length_wf {A}.
Arguments inner_length_wf {A}.
Arguments ostring_wf {A}.