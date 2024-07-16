(* 
  
  Some lemmas that can be used in conjunction with those in Coq.Lists.List
  
  See https://coq.inria.fr/library/Coq.Lists.List.html
 
 *)

 Require Import Lia.
 Require Import Coq.Lists.List.
 Require Import Coq.Arith.Wf_nat.

 Require Import Arith.
 
 Import ListNotations.
 
 (* firstn / skipn / nth_error / map / combine *)
 
 Lemma skipn_skipn {B : Type}: forall n m (l : list B),
   skipn n (skipn m l) = skipn (n + m) l.
 Proof.
     intros n m l. generalize dependent n. generalize dependent l. 
     induction m as [|m' IHm'].
     - simpl. intros. replace (n + 0) with n by lia. reflexivity.
     - intros l n. destruct l as [|h t].
       + simpl. repeat rewrite skipn_nil. reflexivity.
       + simpl. destruct n as [|n'].
         * reflexivity.
         * rewrite IHm'. simpl plus.
           replace (n' + S m') with (S (n' + m')) by lia.
           reflexivity.
 Qed.
 
 
 Lemma nth_error_skipn {X} : forall (xs : list X) i d,
   nth_error xs (i + d) = nth_error (skipn d xs) i.
 Proof.
   intros.
   rewrite <- firstn_skipn with (n := d) (l := xs) at 1.
   assert (d < length xs \/ d >= length xs) as Hxs by lia.
   destruct Hxs.
   - rewrite nth_error_app2.
     + rewrite firstn_length.
       f_equal. lia.
     + rewrite firstn_length.
       lia.
   - rewrite firstn_all2 by lia.
     rewrite skipn_all2 by lia.
     rewrite app_nil_r.
     replace (nth_error (@nil X) i) with (@None X)
       by now destruct i.
     replace (nth_error xs (i + d)) with (@None X).
     auto.
     symmetry. apply nth_error_None. lia.
 Qed.
 
 Lemma nth_error_firstn {X : Type} (l : list X) : forall d i,
   i < d
   -> nth_error (firstn d l) i = nth_error l i.
 Proof.
   intros d i Hdi.
   assert (d <= length l \/ d > length l) as [Hdl | Hdl] by lia.
   + rewrite <- firstn_skipn with (l := l) (n := d) at 2.
   rewrite nth_error_app1. auto.
   rewrite firstn_length. lia.
   + now rewrite firstn_all2 by lia.
 Qed.
 
 Lemma firstn_In {X : Type} : forall (l : list X) n,
   forall x, In x (firstn n l) -> In x l.
 Proof.
   intros.
   rewrite <- (firstn_skipn n l) at 1.
   apply in_or_app. auto.
 Qed.
 
 Lemma skipn_In {X : Type} : forall (l : list X) n,
   forall x, In x (skipn n l) -> In x l.
 Proof.
   intros.
   rewrite <- (firstn_skipn n l) at 1.
   apply in_or_app. auto.
 Qed.
 
 Lemma hd_error_skipn {X : Type} (l : list X) : forall i,
   hd_error (skipn i l) = nth_error l i.
 Proof.
   intro i.
   generalize dependent l. induction i.
   - intro. rewrite skipn_O. destruct l; auto.
   - intro. destruct l; auto.
     simpl. auto.
 Qed.

 Lemma hd_error_snoc_snoc {X : Type} (l : list X) (x1 x2 : X) :
  hd_error ((l ++ [x1]) ++ [x2]) = hd_error (l ++ [x1]).
 Proof.
  destruct l; auto.
 Qed.
 
 Lemma hd_error_nth_error {X : Type} (l : list X) :
   hd_error l = nth_error l 0.
 Proof.
   destruct l; auto.
 Qed.
 
 Lemma nth_error_rev {X : Type} (l : list X) (n : nat) :
   n < length l ->
   nth_error (rev l) n = nth_error l (length l - S n).
 Proof.
   destruct l.
   - simpl. destruct n; reflexivity.
   - intros. remember (x :: l) as l'.
     rewrite nth_error_nth' with (d := x).
     rewrite nth_error_nth' with (d := x).
     f_equal. apply rev_nth.
     auto. lia. auto.
     rewrite rev_length. auto.
 Qed.
 
 Lemma nth_error_Some_ex {X : Type} (l : list X) (n : nat) :
   n < length l <->
   exists x, nth_error l n = Some x.
 Proof.
   split.
   - intros. destruct (nth_error l n) eqn:Hnth.
     + exists x. auto.
     + apply nth_error_None in Hnth. lia.
   - intros [x Hnth]. apply nth_error_Some. congruence.
 Qed.

Lemma skipn_succ_nth_error {X : Type} (l : list X) (n : nat) :
  forall x,
    nth_error l n = Some x ->
    skipn n l = x :: skipn (S n) l.
Proof.
  intros.
  replace l with (firstn n l ++ skipn n l) at 1 by now rewrite firstn_skipn.
  destruct (skipn n l) eqn:Hskipn.
  1 : { specialize (hd_error_skipn l n) as Hhd.
        rewrite Hskipn in Hhd. simpl in Hhd. congruence. }
  specialize (hd_error_skipn l n) as Hhd.
  rewrite Hskipn in Hhd. simpl in Hhd.
  replace x0 with x in * by congruence.
  clear Hhd.
  rewrite skipn_app.
  rewrite skipn_firstn_comm.
  rewrite firstn_length.
  assert (n < length l).
  { rewrite nth_error_Some_ex. now exists x. }
  replace (min n (length l)) with n by lia.
  replace (n - n) with 0 by lia.
  simpl firstn.
  rewrite skipn_O. simpl app.
  f_equal.
  replace (S n) with (1 + n) by lia.
  rewrite <- skipn_skipn.
  rewrite Hskipn.
  reflexivity.
Qed.

Lemma firstn_eq {X : Type} (l1 l2 : list X) (n1 n2 : nat) :
  firstn n1 l1 = firstn n2 l2
  -> (n1 < length l1 /\ n2 < length l2 /\ n1 = n2)
     \/ (n1 >= length l1 /\ length l1 <= length l2 /\ n2 <= n1)
     \/ (n2 >= length l2 /\ length l2 <= length l1 /\ n1 <= n2).
Proof.
  intros.
  assert (n1 < length l1 \/ n1 >= length l1) as [Hn1 | Hn1] by lia.
  - assert (n2 < length l2 \/ n2 >= length l2) as [Hn2 | Hn2] by lia.
    + left. split; [| split]; auto.
      apply f_equal with (f := @length X) in H.
      repeat rewrite firstn_length in H. lia.
    + rewrite -> firstn_all2 with (n := n2) in H by assumption.
      apply f_equal with (f := @length X) in H.
      rewrite firstn_length in H. lia.
  - assert (length l1 <= length l2 \/ length l1 > length l2) as [Hl1 | Hl1] by lia.
    + rewrite -> firstn_all2 with (n := n1) in H by assumption.
      apply f_equal with (f := @length X) in H.
      rewrite firstn_length in H. lia.
    + right. left. split; [| split]; auto.
      * apply f_equal with (f := @length X) in H.
      repeat rewrite firstn_length in H. lia.
      * rewrite -> firstn_all2 with (n := n1) in H by assumption.
        apply f_equal with (f := @length X) in H.
        rewrite firstn_length in H. lia.
Qed. 

Lemma skipn_eq {X : Type} (l1 l2 : list X) (n1 n2 : nat) :
  skipn n1 l1 = skipn n2 l2
  -> (n1 < length l1 /\ n2 < length l2 /\ length l1 - n1 = length l2 - n2)
  \/ (n1 >= length l1 /\ n2 >= length l2)
  .
Proof.
  intros Hskipn.
  assert (n1 < length l1 \/ n1 >= length l1) as [Hn1 | Hn1] by lia.
  - assert (n2 < length l2 \/ n2 >= length l2) as [Hn2 | Hn2] by lia.
    + left. split; [| split]; auto.
      apply f_equal with (f := @length X) in Hskipn.
      repeat rewrite skipn_length in Hskipn. lia.
    + rewrite -> skipn_all2 with (n := n2) in Hskipn by assumption.
      apply f_equal with (f := @length X) in Hskipn.
      rewrite skipn_length in Hskipn. simpl in Hskipn. 
      lia.
  - right.
    apply f_equal with (f := @length X) in Hskipn.
    repeat rewrite skipn_length in Hskipn. simpl in Hskipn.
    lia.
Qed. 

Lemma firstn_eq_slice {X : Type} (l1 l2 : list X) (n n' : nat) :
  firstn n l1 = firstn n l2
  -> n' <= n
  -> firstn n' l1 = firstn n' l2.
Proof.
  intros Hf Hn.
  assert (n >= length l1 \/ n < length l1) as [Hn1 | Hn1] by lia; 
  assert (n >= length l2 \/ n < length l2) as [Hn2 | Hn2] by lia.
  1, 2: rewrite -> firstn_all2 with (l := l1) in Hf by assumption.
  3: rewrite -> firstn_all2 with (l := l2) in Hf by assumption.
  +  rewrite -> firstn_all2 with (n := n) in Hf by lia. congruence.
  +  subst l1. rewrite firstn_firstn. rewrite Nat.min_l by lia. auto.
  +  subst l2. rewrite firstn_firstn. rewrite Nat.min_l by lia. auto.
  + apply f_equal with (f := firstn n') in Hf.
    repeat rewrite -> firstn_firstn in Hf. 
    now replace (min n' n) with n' in Hf by lia.
Qed.

Lemma skipn_eq_slice {X : Type} (l1 l2 : list X) (n n' : nat) :
  skipn n l1 = skipn n l2
  -> n' >= n
  -> skipn n' l1 = skipn n' l2.
Proof.
  intros Hf Hn.
  assert (n >= length l1 \/ n < length l1) as [Hn1 | Hn1] by lia; 
  assert (n >= length l2 \/ n < length l2) as [Hn2 | Hn2] by lia.
  1, 2: rewrite -> skipn_all2 by lia.
  3: rewrite -> skipn_all2 with (l := l2) by lia.
  + now rewrite -> skipn_all2 with (n := n') by lia.
  + rewrite skipn_all2 in Hf by lia.
    apply f_equal with (f := @length X) in Hf.
    rewrite skipn_length in Hf. simpl in Hf.
    now rewrite skipn_all2 by lia.
  + rewrite skipn_all2 with (l := l2) in Hf by lia.
    apply f_equal with (f := @length X) in Hf.
    rewrite skipn_length in Hf. simpl in Hf.
    now rewrite skipn_all2 by lia. 
  + apply f_equal with (f := skipn (n' - n)) in Hf.
    repeat rewrite -> skipn_skipn in Hf. 
    now replace (n' - n + n) with n' in Hf by lia.
Qed.

Lemma app_inv_head_length {X : Type} (l1 l2 l1' l2' : list X) :
  l1 ++ l2 = l1' ++ l2'
  -> length l1 = length l1'
  -> l1 = l1' /\ l2 = l2'.
Proof.
  intros.
  enough (l1 = l1'). {
    subst l1'. apply app_inv_head in H. auto.
  }
  apply f_equal with (f := @firstn X (length l1)) in H.
  repeat rewrite -> firstn_app in H.
  replace (length l1 - length l1) with 0 in H by lia.
  replace (length l1 - length l1') with 0 in H by lia.
  repeat rewrite firstn_O in H. repeat rewrite app_nil_r in H.
  rewrite firstn_all in H. rewrite firstn_all2 in H by lia.
  auto.
Qed.

Lemma app_inv_tail_length {X : Type} (l1 l2 l1' l2' : list X) :
  l1 ++ l2 = l1' ++ l2'
  -> length l2 = length l2'
  -> l1 = l1' /\ l2 = l2'.
Proof.
  intros.
  apply f_equal with (f := @rev X) in H.
  repeat rewrite rev_app_distr in H.
  assert (length (rev l2) = length (rev l2')) as Hlen. {
    now repeat rewrite rev_length.
  }
  apply app_inv_head_length in H. 2 : { auto. }
  destruct H. 
  apply f_equal with (f := @rev X) in H. repeat rewrite rev_involutive in H.
  apply f_equal with (f := @rev X) in H1. repeat rewrite rev_involutive in H1.
  auto.
Qed.

Lemma skipn_tl {X : Type} (l : list X) :
  skipn 1 l = tl l.
Proof.
  destruct l; auto.
Qed.

Lemma map_id {X} : forall (xs : list X),
   map id xs = xs.
 Proof.
   induction xs; auto.
   simpl. rewrite IHxs. auto.
 Qed.
 
 Lemma combine_map {X Y M N} : forall (f : X -> M) (g : Y -> N) xs ys,
   combine (map f xs) (map g ys) = map (fun '(x, y) => (f x, g y)) (combine xs ys).
 Proof.
   induction xs.
   - auto.
   - intros. destruct ys.
     + simpl. auto.
     + simpl. rewrite IHxs. auto.
 Qed.
 
 Lemma combine_app {X Y} : forall (xs1 xs2 : list X) (ys1 ys2 : list Y),
   length xs1 = length ys1
   -> combine (xs1 ++ xs2) (ys1 ++ ys2) = combine xs1 ys1 ++ combine xs2 ys2.
 Proof.
   intros.
   revert ys1 H.
   induction xs1.
   - intros. destruct ys1. auto. simpl in H. discriminate.
   - intros. destruct ys1. simpl in H. discriminate.
     simpl. rewrite IHxs1. auto.
     simpl in H. inversion H. auto.
 Qed.
 
 Lemma combine_rev {X Y} : forall (xs : list X) (ys : list Y),
   length xs = length ys
   -> combine (rev xs) (rev ys) = rev (combine xs ys).
 Proof.
   intros.
   revert ys H.
   induction xs.
   - intros. destruct ys. auto. simpl in H. discriminate.
   - intros. destruct ys. simpl in H. discriminate.
     simpl. simpl in H. inversion H.
     rewrite combine_app. simpl. rewrite IHxs. auto.
     auto.
     repeat rewrite rev_length. auto.
 Qed. 
 
 Lemma map_repeat {X Y : Type} (f : X -> Y) (x : X) n :
   map f (repeat x n) = repeat (f x) n.
 Proof.
   induction n; auto.
   simpl. rewrite IHn. auto.
 Qed.
 
 Lemma repeat_iff {X : Type} (x : X) l:
   l = repeat x (length l) <-> (forall y, In y l -> y = x).
 Proof.
   split.
   - intros. rewrite H in H0.
     apply repeat_spec in H0. auto.
   - intros. apply Forall_eq_repeat.
     apply Forall_forall. firstorder.
 Qed.
 
 (* zipWith *)
 
 Definition zipWith {X Y Z} (f : X -> Y -> Z) (xs : list X) (ys : list Y) : list Z :=
   map (fun '(x, y) => f x y) (combine xs ys).
 
 Lemma zipWith_length {X Y Z} : forall (f : X -> Y -> Z) xs ys,
   length (zipWith f xs ys) = min (length xs) (length ys).
 Proof.
   intros. unfold zipWith.
   now rewrite map_length, combine_length.
 Qed.
 
 Lemma zipWith_In {X Y Z} : forall (P : X -> Prop) (Q : Y -> Prop) (R : Z -> Prop) (f : X -> Y -> Z) xs ys,
   (forall x, In x xs -> P x)
   -> (forall y, In y ys -> Q y)
   -> (forall x y, P x -> Q y -> R (f x y))
   -> forall z, In z (zipWith f xs ys) -> R z.
 Proof.
   intros P Q R f.
   induction xs; intros ys Hxs Hys Hf z Hz.
   - simpl in Hz. inversion Hz.
   - simpl in Hz. destruct ys.
     + inversion Hz.
     + destruct Hz.
       * subst. apply Hf.
         apply Hxs. now left.
         apply Hys. now left.
       * rewrite in_map_iff in H.
         destruct H as [[xx yy] [H1 H2]].
         subst. apply Hf.
         apply Hxs. right.
         now apply in_combine_l in H2.
         apply Hys. right.
         now apply in_combine_r in H2.
 Qed.
 
 Lemma nth_error_zipWith {X Y Z} : forall (f : X -> Y -> Z) xs ys n,
   nth_error (zipWith f xs ys) n = 
   match nth_error xs n, nth_error ys n with
   | Some x, Some y => Some (f x y)
   | _, _ => None
   end.
 Proof.
   intros f. induction xs.
   - intros ys n.
     assert (zipWith f [] ys = []). {
       unfold zipWith. destruct ys; auto.
     }
     rewrite H.
     remember (nth_error [] n) as nz.
     assert (nz = None). {
       subst. destruct n; auto.
     }
     remember (nth_error (@nil X) n) as nx.
     assert (nx = None). {
       subst. destruct n; auto.
     }
     rewrite H0, H1. auto.
   - intros. destruct n.
     + simpl. destruct ys.
       * auto.
       * simpl. auto.
     + destruct ys.
       * simpl. destruct (nth_error xs n); auto.
       * simpl.
         rewrite <- IHxs.
         auto.
 Qed.
 
 Lemma zipWith_cons {X Y Z} : forall (f : X -> Y -> Z) x xs y ys,
   zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys.
 Proof.
   auto.
 Qed.
 
 Lemma zipWith_repeat_l {X Y Z} : forall n (f : X -> Y -> Z) x ys,
   n >= length ys
   -> zipWith f (repeat x n) ys = map (f x) ys.
 Proof.
   induction n.
   - intros. simpl. destruct ys; [auto | simpl in H; lia].
   - intros. destruct ys.
     + simpl. auto.
     + simpl. rewrite zipWith_cons.
       rewrite IHn. auto.
       simpl in H. lia.
 Qed.
 
 Lemma zipWith_repeat_r {X Y Z} : forall n (f : X -> Y -> Z) xs y,
   n >= length xs
   -> zipWith f xs (repeat y n) = map (fun x => f x y) xs.
 Proof.
   induction n.
   - intros. simpl. destruct xs; [auto | simpl in H; lia].
   - intros. destruct xs.
     + simpl. auto.
     + simpl. rewrite zipWith_cons.
       rewrite IHn. auto.
       simpl in H. lia.
 Qed.
 
 Lemma zipWith_firstn_l {X Y Z} : forall (f : X -> Y -> Z) xs ys,
   zipWith f xs ys = zipWith f xs (firstn (length xs) ys).
 Proof.
   unfold zipWith. intros. rewrite combine_firstn_l. auto.
 Qed.
 
 Lemma zipWith_firstn_r {X Y Z} : forall (f : X -> Y -> Z) xs ys,
   zipWith f xs ys = zipWith f (firstn (length ys) xs) ys.
 Proof.
   unfold zipWith. intros. rewrite combine_firstn_r. auto.
 Qed.
 
 Lemma zipWith_firstn {X Y Z} : forall (f : X -> Y -> Z) xs ys,
   zipWith f xs ys = 
     let n := (min (length xs) (length ys)) in 
     zipWith f (firstn n xs) (firstn n ys).
 Proof.
   intros. 
   assert (length xs <= length ys \/ length xs > length ys) as [H | H] by lia.
   - replace (min (length xs) (length ys)) with (length xs) by lia.
     simpl.
     assert (zipWith f xs ys = zipWith f xs (firstn (length xs) ys)) as H1.
     { apply zipWith_firstn_l. }
     assert (zipWith f xs (firstn (length xs) ys) = 
             zipWith f (firstn (length xs) xs) (firstn (length xs) ys)) as H3.
     { f_equal. now rewrite firstn_all. }
     congruence.
   - replace (min (length xs) (length ys)) with (length ys) by lia.
     simpl.
     assert (zipWith f xs ys = zipWith f (firstn (length ys) xs) ys) as H1.
     { apply zipWith_firstn_r. }
     assert (zipWith f (firstn (length ys) xs) ys = 
             zipWith f (firstn (length ys) xs) (firstn (length ys) ys)) as H3.
     { f_equal. now rewrite firstn_all. }
     congruence.
 Qed.
 
 Lemma zipWith_map { M N X Y Z }: forall (f : M -> N -> Z) (g : X -> M) (h : Y -> N) (xs : list X) (ys : list Y),
   zipWith f (map g xs) (map h ys) = map (fun '(x, y) => f (g x) (h y)) (combine xs ys).
 Proof.
   intros. unfold zipWith.
   rewrite combine_map. rewrite map_map.
   apply map_ext. intros. destruct a. auto.
 Qed.
 
 Lemma zipWith_assoc {X}: forall (f : X -> X -> X) xs ys zs,
   (forall x y z, f x (f y z) = f (f x y) z)
   -> zipWith f xs (zipWith f ys zs) = zipWith f (zipWith f xs ys) zs.
 Proof.
   intros f xs.
   remember (length xs) as len.
   generalize dependent xs.
   induction len. 
   - intros. destruct xs. auto. simpl in Heqlen. discriminate.
   - intros. destruct xs.
     + auto. 
     + destruct ys.
       * auto.
       * destruct zs.
         -- auto.
         -- simpl. repeat rewrite zipWith_cons.
            rewrite H. rewrite IHlen.
            ++ auto.
            ++ simpl in Heqlen. inversion Heqlen. auto.
            ++ apply H. 
 Qed.
 
 Lemma zipWith_ext { X Y Z M N } : forall (f : X -> Y -> Z) (g : M -> N -> Z) xs ys ms ns,
   (forall x y m n, In ((x, y), (m, n)) (combine (combine xs ys) (combine ms ns)) -> f x y = g m n)
   -> length xs = length ms
   -> length ys = length ns
   -> zipWith f xs ys = zipWith g ms ns.
 Proof.
   intros f g xs.
   remember (length xs) as len.
   generalize dependent xs.
   induction len. 
   - intros. destruct xs. destruct ms. auto.
     simpl in H0. discriminate. simpl in H0. discriminate.
   - intros. destruct xs. {
     simpl in Heqlen. discriminate.
   } destruct ms. {
     simpl in Heqlen. discriminate.
   } destruct ys. {
     simpl in H1. simpl in H0.
     destruct ns. auto. simpl in H1. discriminate.
   } destruct ns. {
     simpl in H1. discriminate.
   }
   rewrite zipWith_cons. rewrite zipWith_cons.
   simpl in H. f_equal.
   + apply H. auto.
   + apply IHlen.
     1 : { simpl in Heqlen. inversion Heqlen. auto. }
     3 : { simpl in H1. inversion H1. auto. }    
     2 : { simpl in H. firstorder. }
     firstorder.
 Qed.
 
 Lemma zipWith_cons_singleton {X} : forall (xs : list X) (xss : list (list X)),
   zipWith cons xs xss = zipWith (@app X) (map (fun x => [x]) xs) xss.
 Proof.
   intros.
   apply zipWith_ext.
   2 : { now rewrite map_length. }
   2 : { auto. }
   revert xss.
   induction xs.
   - intros. simpl in H. tauto.
   - intros. destruct xss.
     + simpl in H. tauto.
     + simpl in H. destruct H.
       * inversion H. auto.
       * eapply IHxs. eauto.
 Qed. 
 
 Lemma zipWith_rev {X Y Z} : forall (f : X -> Y -> Z) xs ys,
   length xs = length ys
   -> zipWith f (rev xs) (rev ys) = rev (zipWith f xs ys).
 Proof.
   intros. unfold zipWith.
   rewrite combine_rev by assumption.
   apply map_rev.
 Qed.
 
 Lemma zipWith_map2 {X Y Z W : Type} (f : X -> Y -> Z) (g : Z -> W) (xs : list X) (ys : list Y) :
   map g (zipWith f xs ys) = zipWith (fun x y => g (f x y)) xs ys.
 Proof.
   unfold zipWith at 2.
   replace (map (fun '(x, y) => g (f x y)) (combine xs ys))
     with (map g (map (fun '(x, y) => f x y) (combine xs ys))). 2: {
     rewrite map_map. apply map_ext_in. intros [x y]. auto.
   } 
   auto.
 Qed.
 
 Lemma zipWith_ext_id_l {X Y : Type} (f : X -> Y -> X) (xs : list X) (ys : list Y) :
   (forall x y, In (x, y) (combine xs ys) -> f x y = x)
   -> length xs <= length ys
   -> zipWith f xs ys = xs.
 Proof.
   remember (length xs) as len.
   generalize dependent xs.
   generalize dependent ys.
   induction len.
   - intros. destruct xs; destruct ys; auto.
     simpl in Heqlen. discriminate.
     simpl in H0. discriminate.
   - intros. destruct xs; destruct ys; auto.
     + simpl in H0. lia.
     + simpl in H. rewrite zipWith_cons.
       f_equal.
       * specialize (H x y). auto.
       * apply IHlen. 
         simpl in Heqlen. lia.
         intros. apply H. auto. 
         simpl in H0. lia.
 Qed.
 
 Lemma zipWith_ext_id_r {X Y : Type} (f : X -> Y -> Y) (xs : list X) (ys : list Y) :
   (forall x y, In (x, y) (combine xs ys) -> f x y = y)
   -> length xs >= length ys
   -> zipWith f xs ys = ys.
 Proof.
   remember (length xs) as len.
   generalize dependent xs.
   generalize dependent ys.
   induction len.
   - intros. destruct xs; destruct ys; auto.
     simpl in H0. lia.
     simpl in H0. discriminate.
   - intros. destruct xs; destruct ys; auto.
     + simpl in H0. discriminate.
     + simpl in H. rewrite zipWith_cons.
       f_equal.
       * specialize (H x y). auto.
       * apply IHlen. 
         simpl in Heqlen. lia.
         intros. apply H. auto. 
         simpl in H0. lia.
 Qed.
 
 (* transpose *)
 
 Fixpoint transpose {X : Type} (len : nat) (tapes : list (list X)) : list (list X) :=
   match tapes with
   | [] => repeat [] len
   | t :: ts => zipWith cons t (transpose len ts)
   end.
 
   Lemma transpose_length {X : Type} : forall len (tapes : list (list X)),
   (forall t, 
     In t tapes -> length t >= len)
   -> length (transpose len tapes) = len.
 Proof.
   intros len tapes. revert len.
   induction tapes; intros len Hlen.
   - simpl. now rewrite repeat_length.
   - simpl. rewrite zipWith_length.
     rewrite IHtapes.
     + simpl in Hlen. specialize (Hlen a).
       assert (length a >= len) by auto.
       lia.
     + intros t Ht. apply Hlen. now right.
 Qed.
 
 Lemma transpose_inner_length {X : Type}: forall len (tapes : list (list X)),
   forall u,
     In u (transpose len tapes)
     -> length u = length tapes.
 Proof.
   intros len tapes. revert len.
   induction tapes; intros len u Hu.
   - simpl in *. apply repeat_spec in Hu.
     subst. auto.
   - simpl in *.
     unfold zipWith in Hu.
     rewrite in_map_iff in Hu.
     destruct Hu as [[u1 us] [Hu Hus]].
     apply in_combine_r in Hus.
     subst. simpl. f_equal.
     firstorder.
 Qed.
 
 Lemma transpose_inner_length_eq {X : Type} : forall len (tapes : list (list X)),
   forall u v,
     In u (transpose len tapes)
     -> In v (transpose len tapes)
     -> length u = length v.
 Proof.
   intros.
   apply transpose_inner_length in H.
   apply transpose_inner_length in H0.
   congruence.
 Qed.
 
 Lemma transpose_app {X : Type} : forall len (tapes1 tapes2 : list (list X)),
   (forall t, In t tapes1 -> length t >= len)
   -> (forall t, In t tapes2 -> length t >= len)
   -> transpose len (tapes1 ++ tapes2) = 
   zipWith (@app X) (transpose len tapes1) (transpose len tapes2).
 Proof.
   intros len tapes1 tapes2 Ht1 Ht2.
   induction tapes1.
   - simpl.
     rewrite zipWith_repeat_l.
     rewrite <- map_id with (xs := transpose _ _) at 1.
     apply map_ext. auto.
     rewrite transpose_length. auto. auto.
   - simpl. rewrite IHtapes1.
     + rewrite zipWith_cons_singleton.
       rewrite zipWith_cons_singleton.
       rewrite zipWith_assoc by apply app_assoc.
       auto.
     + simpl in Ht1. firstorder.  
 Qed.
 
 Lemma transpose_singleton {X : Type} : forall (t : list X),
   transpose (length t) [t] = map (fun x => [x]) t.
 Proof.
   intros. unfold transpose. 
   now rewrite zipWith_repeat_r by lia.
 Qed.
 
 Lemma transpose_rev_aux {X : Type} : forall (xss : list (list X)) (l : list X),
   (forall t u, In t xss -> In u xss -> length t = length u)
   -> zipWith (@app X) (map (@rev X) xss) (map (fun x => [x]) l) 
     = map (@rev X) (zipWith (@app X) (map (fun x => [x]) l) xss).
 Proof.
   induction xss as [ | xs xss].
   - intros. simpl.
     destruct l.
     + auto.
     + simpl. unfold zipWith. auto.
   - intros. destruct l.
     + simpl. unfold zipWith. auto.
     + simpl map at 1 2. rewrite zipWith_cons.
       simpl map at 3. f_equal.
       rewrite IHxss. auto.
       simpl in H. firstorder.
 Qed.
 
 Lemma transpose_rev {X : Type} : forall len (tapes : list (list X)),
   (forall t, In t tapes -> length t = len)
   -> transpose len (rev tapes) = map (@rev X) (transpose len tapes).
 Proof.
   intros len tapes Hlen.
   induction tapes.
   - simpl. rewrite <- map_id with (xs := repeat [] len) at 1.
     apply map_ext_in. intros.
     apply repeat_spec in H. subst. auto.
   - simpl. simpl in Hlen.
     assert (length a = len) as Ha. {
       apply Hlen. auto.
     }
     rewrite transpose_app.
     rewrite IHtapes.
     rewrite zipWith_cons_singleton.
     rewrite <- Ha.
     rewrite transpose_singleton.
     rewrite transpose_rev_aux. auto.
     + apply transpose_inner_length_eq.
     + auto.
     + intros. rewrite <- in_rev in H.
       enough (length t = len) by lia. auto.
     + simpl. intros. 
       enough (length t = len) by lia. firstorder.
 Qed.
 
 Lemma transpose_zipWith_cons {X : Type} : forall len (mat : list (list X)) t,
     (forall u, In u mat -> length u >= len) 
   -> length t = length mat
   -> transpose (S len) (zipWith cons t mat) = t :: transpose len mat.
 Proof.
   intros len mat. revert len. induction mat as [ | t1 mat1 IHmat].
   - intros. simpl. destruct t; auto. simpl in H0. discriminate.
   - intros. simpl. destruct t.
     + simpl in H0. discriminate.
     + rewrite zipWith_cons.
       simpl transpose. rewrite IHmat.
       * now rewrite zipWith_cons.
       * simpl in H. firstorder.
       * simpl in H0. now inversion H0.
 Qed.
 
 
 Lemma transpose_involutive {X : Type} : forall len (tapes : list (list X)),
   (forall t, In t tapes -> length t = len)
   -> transpose (length tapes) (transpose len tapes) = tapes.
 Proof.
   intros len tapes. revert len.
   induction tapes as [ | t tapes1 IHtapes].
   - simpl. intros.
     destruct len; auto.
   - intros. simpl. rewrite transpose_zipWith_cons.
     + rewrite IHtapes. auto.
       simpl in H. firstorder.
     + simpl in H. intros.
       enough (length u = length tapes1) by lia.
       apply transpose_inner_length with (len := len).
       auto.
     + rewrite transpose_length.
       * simpl in H. apply H. auto.
       * simpl in H. intros.
         enough (length t0 = len) by lia.
         apply H. auto.
 Qed.
 
 Lemma transpose_rev2 {X : Type} : forall len (tapes : list (list X)),
   (forall t, In t tapes -> length t = len)
   -> rev (transpose len tapes) = transpose len (map (@rev X) tapes).
 Proof.
   intros len tapes Hlen.
   pose proof (@transpose_rev X (length tapes) (transpose len tapes)).
   assert (forall t, In t (transpose len tapes) -> length t = length tapes) as Hlen2. {
     intros; now apply transpose_inner_length in H0.
   }
   specialize (H Hlen2).
   rewrite transpose_involutive in H.
   apply (f_equal (fun x => transpose len x)) in H.
   replace len with (length (rev (transpose len tapes))) in H at 1. 2 :{
     rewrite rev_length. rewrite transpose_length. auto.
     intros. enough (length t = len) by lia. auto.
   }
   rewrite transpose_involutive in H. auto.
   - intros. rewrite <- in_rev in H0.
     now apply transpose_inner_length with (len := len).
   - auto.  
   (* (1) from transpose_rev: transpose (rev tapes) = map rev (transpose tapes)
      (2) plugin (tapes := transpose tapes): 
             transpose (rev (transpose tapes)) 
           = map rev (transpose (transpose tapes)) 
           = map rev tapes 
       (3) apply transpose to both sides.
   *)
 Qed.
 
 Lemma transpose_firstn {X : Type} : forall len (tapes : list (list X)) n,
   (forall t, In t tapes -> length t >= len)
   -> transpose len (firstn n tapes) = map (firstn n) (transpose len tapes).
 Proof.
   intros len tapes n Hlen.
   assert (n > length tapes \/ n <= length tapes) as [Hn | Hn] by lia. {
     rewrite firstn_all2 by lia.
     rewrite map_ext_in with (g := id).
     now rewrite map_id.
     intros. simpl.
     rewrite firstn_all2.
     auto. apply transpose_inner_length in H. lia.
   }
   rewrite <- firstn_skipn with (l := tapes) (n := n) at 2.
   rewrite transpose_app. rewrite zipWith_map2.
   rewrite zipWith_ext_id_l. auto.
   - intros. rewrite firstn_app.
     enough (n = length x). {
       rewrite H0.
       replace (length x - length x) with 0 by lia.
       rewrite firstn_O. rewrite firstn_all. apply app_nil_r.
     }
     apply in_combine_l in H.
     apply transpose_inner_length in H.
     rewrite firstn_length in H.
     lia.
   - repeat rewrite transpose_length. auto.
     * intros. apply skipn_In in H. auto.
     * intros. apply firstn_In in H. auto.
   - intros. apply firstn_In in H. auto.
   - intros. apply skipn_In in H. auto.
 Qed.
 
 Lemma transpose_skipn {X : Type} : forall len (tapes : list (list X)) n,
   (forall t, In t tapes -> length t >= len)
   -> transpose len (skipn n tapes) = map (skipn n) (transpose len tapes).
 Proof.
   intros len tapes n Hlen.
   assert (n > length tapes \/ n <= length tapes) as [Hn | Hn] by lia. {
     rewrite skipn_all2 by lia.
     simpl. revert Hn.
     induction tapes.
     - simpl. rewrite map_repeat. destruct n; auto.
     - simpl. intros. rewrite zipWith_map2. unfold zipWith.
       rewrite map_ext_in with (g := (fun x => [])). 2 : {
         intros. destruct a0. 
         pose proof H as H0.
         apply in_combine_l in H.
         apply in_combine_r in H0.
         apply skipn_all2.
         simpl. apply transpose_inner_length in H0.
         lia.
       } 
       assert (length (combine a (transpose len tapes)) = len). {
         rewrite combine_length. simpl in Hlen.
         rewrite transpose_length. specialize (Hlen a ltac:(auto)). lia.
         auto.
       }
       remember (map _ (combine _ _)) as rhs.
       assert (rhs = repeat [] (length rhs)). {
         rewrite repeat_iff. subst rhs. intros.
         apply in_map_iff in H0. destruct H0 as [? [? ?]].
         auto.
       }
       rewrite Heqrhs in H0 at 2. rewrite map_length in H0.
       rewrite H in H0. auto.
   }
   rewrite <- firstn_skipn with (l := tapes) (n := n) at 2.
   rewrite transpose_app. rewrite zipWith_map2.
   rewrite zipWith_ext_id_r. auto.
   - intros. rewrite skipn_app.
     enough (n = length x). {
       rewrite H0.
       replace (length x - length x) with 0 by lia.
       rewrite skipn_O. rewrite skipn_all. auto.
     }
     apply in_combine_l in H.
     apply transpose_inner_length in H.
     rewrite firstn_length in H.
     lia.
   - repeat rewrite transpose_length. auto.
     * intros. apply skipn_In in H. auto.
     * intros. apply firstn_In in H. auto.
   - intros. apply firstn_In in H. auto.
   - intros. apply skipn_In in H. auto.
 Qed.
 
 Lemma skipn_zipWith_cons {X : Type} (xs : list X) (xss : list (list X)) :
  length xs >= length xss
   -> map (skipn 1) (zipWith cons xs xss) = xss.
 Proof.
   generalize dependent xs.
   induction xss; intros.
   - destruct xs; auto.
   - destruct xs.
     + simpl in H. lia.
     + rewrite zipWith_cons.
       rewrite map_cons.
       simpl skipn at 1.
       f_equal. apply IHxss. 
       simpl in H. lia.
 Qed.
 
 (* augmentVString *)
 
 Definition augmentVString {X : Type} (vstring : list (list X)) (tape : list X) : list (list X) :=
   zipWith (@app X) vstring (map (fun x => [x]) tape).
 
 Lemma augmentVString_length {X : Type} : forall (vstring : list (list X)) (tape : list X),
   length tape >= length vstring
   -> length (augmentVString vstring tape) = length vstring.
 Proof.
   intros. unfold augmentVString.
   rewrite zipWith_length. rewrite map_length. 
   lia.
 Qed.
 
 Lemma augmentVString_inner_length {X : Type} : forall (vstring : list (list X)) (tape : list X) i,
   i < length vstring
   -> forall val, nth_error (augmentVString vstring tape) i = Some val
   -> exists val', nth_error vstring i = Some val' /\ length val = S (length val').
 Proof.
   intros.
   unfold augmentVString in H0.
   rewrite nth_error_zipWith in H0.
   destruct (nth_error vstring i) eqn:Heq; try discriminate.
   destruct (nth_error (map (fun x : X => [x]) tape) i) eqn:Heq2; try discriminate.
   inversion H0.
   exists l. split; [auto | ].
   rewrite app_length. enough (length l0 = 1) by lia.
   rewrite nth_error_map in Heq2.
   unfold option_map in Heq2.
   destruct (nth_error tape i); try discriminate.
   inversion Heq2. auto.
 Qed.
 
 Lemma augmentVString_inner_length_eq {X : Type} : forall (vstring : list (list X)) (tape : list X),
   length tape >= length vstring
   -> (forall u v, In u vstring -> In v vstring -> length u = length v)
   -> (forall u v, In u (augmentVString vstring tape) -> In v (augmentVString vstring tape) -> length u = length v).
 Proof.
   intros.
   apply In_nth_error in H1, H2.
   destruct H1 as [i1 Hi1], H2 as [i2 Hi2].
   assert (i1 < length vstring). {
     rewrite <- augmentVString_length with (tape := tape) by auto.
     apply nth_error_Some. congruence.
   }
   assert (i2 < length vstring). {
     rewrite <- augmentVString_length with (tape := tape) by auto.
     apply nth_error_Some. congruence.
   }
   apply augmentVString_inner_length in Hi1; [ | auto].
   apply augmentVString_inner_length in Hi2; [ | auto].
   destruct Hi1 as [u1 [Hu1 Hu1len]].
   destruct Hi2 as [u2 [Hu2 Hu2len]].
   rewrite Hu1len, Hu2len. f_equal.
   apply nth_error_In in Hu1.
   apply nth_error_In in Hu2.
   apply H0; auto.
 Qed.
 
 Lemma augmentVString_transpose {X : Type} : forall (vstring : list (list X)) (tape : list X) len,
   (forall val, In val vstring -> length val = len)
   -> length tape = length vstring
   -> transpose (length tape) (transpose len vstring ++ [tape]) = augmentVString vstring tape.
 Proof.
   intros.
   rewrite transpose_app. 2 : {
     intros. apply transpose_inner_length in H1.
     lia.
   } 2 : {
     simpl. firstorder. subst. auto.
   }
   rewrite transpose_singleton.
   rewrite H0.
   rewrite transpose_involutive by assumption.
   unfold augmentVString.
   reflexivity.
 Qed.
 
 Lemma augmentVString_transpose_1 {X : Type} : forall (vstring : list (list X)) (tape : list X) len,
 (forall val, In val vstring -> length val = len)
 -> length tape = length vstring
 -> transpose (S len) (augmentVString vstring tape) = transpose len vstring ++ [tape].
 Proof.
   intros.
   rewrite <- augmentVString_transpose with (len := len) by auto.
   assert (S len = length (transpose len vstring ++ [tape])) as Hlen. {
     rewrite app_length. rewrite transpose_length. simpl. lia.
     intros t Hx. apply H in Hx. lia. 
   }
   rewrite Hlen. rewrite transpose_involutive. auto.
   intros. apply in_app_iff in H1. destruct H1.
   - apply transpose_inner_length in H1. congruence.
   - simpl in H1. firstorder. congruence.
 Qed. 
 
 (* ij_error *)
 
 Definition ij_error {X : Type} (i j : nat) (l : list (list X)) : option X :=
   match nth_error l i with
   | Some l' => nth_error l' j
   | None => None
   end.
 
 Lemma ij_error_remove_rows {X : Type} (i j d : nat) (l : list (list X)) :
   ij_error (i + d) j l = ij_error i j (skipn d l).
 Proof.
   unfold ij_error.
   rewrite nth_error_skipn.
   auto.
 Qed.
 
 Lemma ij_error_remove_cols {X : Type} (i j d : nat) (l : list (list X)) :
   ij_error i (j + d) l = ij_error i j (map (skipn d) l).
 Proof.
   unfold ij_error.
   remember (nth_error l i) as row_i.
   destruct row_i.
   2 : {
     symmetry in Heqrow_i. 
     rewrite nth_error_None in Heqrow_i.
     assert (nth_error (map (skipn d) l) i = None). {
       rewrite nth_error_None.
       now rewrite map_length.
     }
     rewrite H. auto.
   }
   assert (length l > i) as Hlen. {
     symmetry in Heqrow_i.
     assert (nth_error l i <> None) by congruence.
     rewrite nth_error_Some in H.
     lia.
   }
   remember (nth_error (map (skipn d) l) i) as row_i'.
   destruct row_i'.
   2 : {
     symmetry in Heqrow_i'.
     rewrite nth_error_None in Heqrow_i'.
     rewrite map_length in Heqrow_i'. lia.
   }
   rewrite nth_error_map in Heqrow_i'.
   rewrite <- Heqrow_i in Heqrow_i'. simpl in Heqrow_i'.
   inversion Heqrow_i'. subst.
   now rewrite nth_error_skipn.
 Qed.
 
 Lemma transpose_spec_0 {X : Type} : forall (xs : list X) (xss : list (list X)) i,
   length xss = length xs
   -> nth_error xs i = ij_error i 0 (zipWith cons xs xss).
 Proof.
   induction xs.
   - intros. simpl. destruct i; auto.
   - intros xss. destruct i.
     + intros. simpl. unfold ij_error.
       destruct xss.
       * simpl in H. lia.
       * simpl. auto.
     + intros. simpl. unfold ij_error.
       destruct xss.
       * simpl in H. lia.
       * rewrite zipWith_cons.
         simpl nth_error. 
         rewrite IHxs with (xss := xss).
         auto. simpl in H. lia.
 Qed. 
 
 Lemma transpose_spec {X : Type} : forall len (tapes : list (list X)),
   (forall t,
     In t tapes -> length t = len)
   -> forall i j,
     ij_error i j tapes = ij_error j i (transpose len tapes).
 Proof.
   induction tapes as [|l tapes IHt]; simpl; intros H.
 - (* when the matrix is empty *)
   intros i j.
   destruct i.
   + unfold ij_error at 1. simpl.
     unfold ij_error. 
     assert (j < len \/ j >= len) by lia.
     destruct H0.
     ++ rewrite nth_error_repeat by apply H0.
        auto.
     ++ assert (nth_error (repeat (@nil X) len) j = None). {
          rewrite nth_error_None by lia.
          rewrite repeat_length.
          auto.
        }
        rewrite H1. auto.
   + unfold ij_error at 1. simpl.
     unfold ij_error. 
     assert (j < len \/ j >= len) by lia.
     destruct H0.
     ++ rewrite nth_error_repeat by apply H0.
        auto.
     ++ assert (nth_error (repeat (@nil X) len) j = None). {
          rewrite nth_error_None by lia.
          rewrite repeat_length.
          auto.
        }
        rewrite H1. auto. 
 - destruct i.
   + (* ij_error 0 j and ij_error j 0 *)
     intros j.
     unfold ij_error at 1. simpl.
     apply transpose_spec_0.
     rewrite transpose_length.
     symmetry. apply H. auto.
     intros. enough (length t = len) by lia.
     apply H. auto.
   + (* ij_error (S i) j and ij_error j (S i *)
     replace (S i) with (i + 1) by lia. intros.
     rewrite ij_error_remove_cols.
     rewrite ij_error_remove_rows.
     simpl skipn at 1.
     rewrite IHt. 
     rewrite skipn_zipWith_cons. auto.
     * rewrite transpose_length.
       enough (length l = len) by lia.
       apply H. auto.
       intros.
       enough (length t = len) by lia.
       apply H. auto.
     * intros. 
       enough (length t = len) by lia.
       apply H. auto.
 Qed.
 
 (* select *)
 
 Fixpoint select {X} (selector : list nat) (selectee : list X) : option (list X) :=
   match selector with
   | [] => Some []
   | n :: ns =>
     match nth_error selectee n with
     | Some x => 
       match select ns selectee with
       | Some xs => Some (x :: xs)
       | None => None
       end
     | None => None
     end
   end.
 
 Lemma select_app_Some {X : Type} (selector1 selector2 : list nat) (selectee : list X) :
   forall result1 result2,
   select selector1 selectee = Some result1 ->
   select selector2 selectee = Some result2 ->
   select (selector1 ++ selector2) selectee = Some (result1 ++ result2).
 Proof.
   revert selector2.
   induction selector1.
   - intros. simpl in *. inversion H. subst. simpl. assumption.
   - intros. simpl in *. destruct (nth_error selectee a) eqn:E.
     + destruct (select selector1 selectee) eqn:E2.
       * inversion H. subst. simpl. 
         rewrite IHselector1 with (selector2 := selector2) (result1 := l) (result2 := result2); auto.
       * inversion H.
     + inversion H.
 Qed.
 
 Lemma select_app_None_r {X : Type} (selector1 selector2 : list nat) (selectee : list X) :
   select selector2 selectee = None ->
   select (selector1 ++ selector2) selectee = None.
 Proof.
   revert selector2.
   induction selector1.
   + intros. rewrite app_nil_l. assumption.
   + intros. simpl.
     apply IHselector1 in H.
     rewrite H. destruct (nth_error selectee a); auto.
 Qed.
 
 Lemma select_defined {X : Type} : forall (selector : list nat) (selectee : list X),
   (forall n, In n selector -> n < length selectee) <->
   exists result, select selector selectee = Some result.
 Proof.
   split.
   { induction selector.
   - intros. exists []. auto.
   - intros.
     simpl in H.
     assert (a < length selectee) by (apply H; left; auto).
     assert (forall n, In n selector -> n < length selectee) 
       by (intros; apply H; right; auto).
     clear H.
     specialize (IHselector H1).
     destruct IHselector as [result IH].
     pose proof (nth_error_Some_ex selectee a).
     rewrite H in H0. destruct H0 as [x H0].
     exists (x :: result).
     simpl. rewrite H0. rewrite IH. auto.
   }
   { intros. destruct H as [result H].
     generalize dependent selectee.
     revert result.
     induction selector.
     - simpl in H0. contradiction.
     - intros. simpl in *. destruct H0.
       + subst. destruct (nth_error selectee n) eqn:E.
         * apply nth_error_Some. congruence.
         * congruence.
       + destruct (nth_error selectee a) eqn:E;
         destruct (select selector selectee) eqn:E2; try congruence.
         apply IHselector with (result := l); auto.
   }
 Qed.
 
 Lemma select_app_None_l {X : Type} (selector1 selector2 : list nat) (selectee : list X) :
   select selector1 selectee = None ->
   select (selector1 ++ selector2) selectee = None.
 Proof.
   intros.
   destruct (select (selector1 ++ selector2) selectee) eqn:E1.
   2 : auto.
   assert (exists result, select (selector1 ++ selector2) selectee = Some result)
     by now exists l.
   rewrite <- select_defined in H0.
   setoid_rewrite in_app_iff in H0.
   assert (forall n, In n selector1 -> n < length selectee) as H1. {
     intros. apply H0. left. auto.
   }
   apply select_defined in H1 as [result1 H1].
   congruence.
 Qed.
 
 Lemma select_length {X : Type} : forall (selector : list nat) (selectee : list X) result,
   select selector selectee = Some result ->
   length selector = length result.
 Proof.
   induction selector.
   - intros. simpl in *. inversion H. auto.
   - intros. simpl in *. destruct (nth_error selectee a) eqn:E.
     + destruct (select selector selectee) eqn:E2.
       * inversion H. subst. simpl. f_equal. 
         now apply IHselector with (selectee := selectee).
       * inversion H.
     + inversion H.
 Qed.
 
 (* collectSome *)
 
 Definition collectSome {X} (l : list (option X)) : list X :=
   flat_map (fun x => match x with Some x => [x] | None => [] end) l.
 
 Lemma collectSome_app {X} : forall (l1 l2 : list (option X)),
   collectSome (l1 ++ l2) = collectSome l1 ++ collectSome l2.
 Proof.
   intros. unfold collectSome.
   rewrite flat_map_app. auto.
 Qed.
 
 Lemma collectSome_cons {X} : forall (l : list (option X)) (x : option X),
   collectSome (x :: l) = 
     match x with Some x => x :: collectSome l | None => collectSome l end.
 Proof.
   intros. unfold collectSome.
   simpl. destruct x; auto.
 Qed.
 
 Lemma collectSome_length {X} : forall (l : list (option X)),
   (forall x, In x l -> x <> None)
   -> length (collectSome l) = length l.
 Proof.
   intros.
   induction l.
   - auto.
   - simpl. destruct a eqn:E.
     + simpl. f_equal. apply IHl.
       intros. apply H. now right.
     + specialize (H None). simpl in H.
       firstorder.
 Qed.
 
 Lemma collectSome_length_le {X} : forall (l : list (option X)),
   length (collectSome l) <= length l.
 Proof.
   intros. unfold collectSome.
   induction l.
   - simpl. lia.
   - simpl. destruct a; simpl; lia.
 Qed.
 
 Lemma collectSome_In {X} : forall (l : list (option X)) x,
   In x (collectSome l)
   <-> In (Some x) l.
 Proof.
   intros.
   split.
   - intros. induction l.
     + simpl in H. tauto.
     + rewrite collectSome_cons in H.
       destruct a eqn:E.
       * simpl in H. destruct H.
         ** subst. constructor. auto.
         ** right. apply IHl. auto.
       * right. apply IHl. auto. 
   - intros. induction l.
     + simpl. tauto.
     + rewrite collectSome_cons.
       destruct a eqn:E.
       * simpl. destruct H.
         ** inversion H. auto.
         ** right. apply IHl. auto.
       * apply IHl. destruct H.
         ** inversion H.
         ** auto.
 Qed.
 
 (* maximum *)
 
 Definition maximum (l : list nat) : nat :=
   fold_right max 0 l.
 
 Lemma maximum_app (l1 l2 : list nat) :
   maximum (l1 ++ l2) = max (maximum l1) (maximum l2).
 Proof.
   induction l1.
   - auto.
   - simpl. rewrite IHl1. lia.
 Qed.
 
 Lemma maximum_In (l : list nat) :
   forall x, In x l -> x <= maximum l.
 Proof.
   induction l.
   - intros. simpl in *. tauto.
   - intros. simpl in *. destruct H.
     + subst. lia.
     + specialize (IHl x H). lia.
 Qed.
 
 (* unsnoc *)
 
 Fixpoint unsnoc {X : Type} (l : list X) : option (list X * X) :=
   match l with
   | [] => None
   | x :: l' => match unsnoc l' with
     | None => Some ([], x)
     | Some (l'', x') => Some (x :: l'', x')
     end
   end.
 
 Lemma last_inversion {A : Type} : forall (x y : A) xs ys,
     xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
 Proof.
   intros. apply (f_equal (@rev A)) in H.
   repeat rewrite (rev_app_distr) in H.
   simpl in H. inversion H. apply (f_equal (@rev A)) in H2.
   repeat rewrite rev_involutive in H2.
   auto.
 Qed.
 
 Lemma unsnoc_spec {X : Type} : forall (l : list X) (l' : list X),
   (forall x, unsnoc l = Some (l', x) <-> l = l' ++ [x])
   /\ (unsnoc l = None <-> l = []).
 Proof.
   induction l.
   - simpl. intros. repeat split. try discriminate.
     intros. destruct l'; discriminate.
   - destruct (unsnoc l) eqn:E.
     + destruct p as [l1 x1].
       intros. split.
       * intros. simpl. rewrite E. 
         specialize (IHl l1).
         destruct IHl as [IHl1 IHl2].
         specialize (IHl1 x1).
         assert (l = l1 ++ [x1]) as H. {
           apply IHl1. auto.
         }
         rewrite H. 
         split. intros.
         ** inversion H0.  auto. 
         ** intros. 
            replace (a :: l1 ++ [x1]) with ((a :: l1) ++ [x1]) in H0 by auto.
            apply last_inversion in H0. destruct H0. subst. auto.
       * intros. split; [ | discriminate].
         simpl. rewrite E. intros. inversion H.
     + simpl.
        assert (l = []) as H. {
         specialize (IHl []) as [IHl1 IHl2].
         apply IHl2. auto.
        }
        subst l. simpl.
        repeat split; try discriminate.
        * intros. inversion H. subst. reflexivity.
        * intros. 
          replace ([a]) with ([] ++ [a]) in H by auto.
          apply last_inversion in H. destruct H. subst. auto.
 Qed.
 
 Lemma unsnoc_Some {X : Type} : forall (l : list X) (l' : list X) (x : X),
   (unsnoc l = Some (l', x) <-> l = l' ++ [x]).
 Proof.
   intros. apply unsnoc_spec.
 Qed.
 
 Lemma unsnoc_None {X : Type} : forall (l : list X),
   (unsnoc l = None <-> l = []).
 Proof.
   intros. apply unsnoc_spec. exact [].
 Qed.
 
 Lemma unsnoc_Some_ex_ne {X : Type} : forall (l : list X),
   l <> [] -> exists l' x, unsnoc l = Some (l', x).
 Proof.
   intros. destruct (unsnoc l) eqn:E.
   - destruct p as [l' x]. exists l', x. auto.
   - rewrite unsnoc_None in E. congruence.
 Qed.
 
 Lemma unsonc_Some_ex {X : Type} : forall (x : X) (l : list X),
   exists l' y, unsnoc (x :: l) = Some (l', y).
 Proof.
   intros. pose proof (unsnoc_Some_ex_ne (x :: l)) as H.
   specialize (H ltac:(discriminate)).
   auto.
 Qed.
 
 Lemma unsnoc_length {X : Type} : forall (l : list X) (l' : list X) (x : X),
   unsnoc l = Some (l', x) -> length l = S (length l').
 Proof.
   intros. apply unsnoc_Some in H. subst.
   rewrite app_length. simpl. lia.
 Qed.
 
 Definition last_error {X : Type} (l : list X) : option X :=
   match unsnoc l with
   | Some (_, x) => Some x
   | None => None
   end.
 
 Lemma last_error_Some {X : Type} : forall (l : list X) (x : X),
   last_error l = Some x <-> exists l', l = l' ++ [x].
 Proof.
   intros. unfold last_error.
   destruct (unsnoc l) eqn:E.
   - destruct p as [l' x'].
     rewrite unsnoc_Some in E. subst.
     split; intros.
     + inversion H. exists l'. auto.
     + destruct H as [l'' H]. 
       apply last_inversion in H. destruct H.
       subst. auto.
   - split.
     + intros. discriminate.
     + intros. destruct H as [l'' H]. subst.
       rewrite unsnoc_None in E. 
       destruct l''; discriminate.
 Qed.

Lemma last_error_snoc {X : Type} : forall (x : X) (l : list X),
  last_error (l ++ [x]) = Some x.
Proof.
  intros. rewrite last_error_Some.
  exists l. auto.
Qed.

Lemma last_error_None {X : Type} : forall (l : list X),
  last_error l = None <-> l = [].
Proof.
  intros l.
  destruct (unsnoc l) as [[l' x ]| ] eqn:El.
  - rewrite unsnoc_Some in El. split.
    + intros. subst l. rewrite last_error_snoc in H.
      discriminate.
    + intros. subst.
      apply f_equal with (f := @length X) in H.
      rewrite app_length in H. simpl in H. lia.
  -  rewrite unsnoc_None in El. split
    + intros. subst l. auto.
    + intros. subst. auto.
Qed.


Lemma last_error_cons_cons {X : Type} : forall (x y : X) (l : list X),
  last_error (x :: y :: l) = last_error (y :: l).
Proof.
  intros. unfold last_error.
  simpl. 
  destruct (unsnoc l) eqn:E.
  - destruct p. auto.
  - auto.
Qed.

Lemma last_error_nth_error {X : Type} : forall (l : list X),
  last_error l = nth_error l (length l - 1).
Proof.
  intros. unfold last_error.
  destruct (unsnoc l) eqn:E.
  - destruct p. rewrite unsnoc_Some in E. rewrite E.
    rewrite nth_error_app2. rewrite app_length. simpl.
    replace (length l0 + 1 - 1 - length l0) with 0 by lia.
    auto.
    rewrite app_length. simpl. lia.
  - rewrite unsnoc_None in E. subst. auto.
Qed.

 
 (* filter *)
 
 Lemma filter_index : forall {X : Type} (l : list X) (f : X -> bool) (x : X) (i : nat),
   nth_error (filter f l) i = Some x
   -> exists j, 
     nth_error l j = Some x
     /\ i <= j.
 Proof.
   induction l.
   { intros. simpl in H. destruct i; inversion H. }
   intros; simpl in H.
   destruct (f a) eqn:Hfa.
   - intros.
     destruct i.
     + simpl in H. inversion H. subst a. clear H.
       exists 0. split; [reflexivity | lia].
     + simpl in H.
       destruct (IHl f x i H) as [j [Hj Hij]].
       exists (S j). split; [assumption | lia].
   - intros.
     destruct (IHl f x i H) as [j [Hj Hij]].
     exists (S j). split; [assumption | lia].
 Qed.
 
 
 Lemma filter_order {X : Type} (l : list X) (f : X -> bool):
   forall x y i j,
     i < j
     -> nth_error (filter f l) i = Some x
     -> nth_error (filter f l) j = Some y
     -> exists i' j',
         i' < j'
      /\ nth_error l i' = Some x
      /\ nth_error l j' = Some y.
 Proof.
   induction l.
   { intros. simpl in H0. destruct i; inversion H0. }
   destruct (f a) eqn:Hfa.
   - intros. 
     pose proof (filter_index (a :: l) _ _ _ H0) as [i' [Hi' Hii']].
     pose proof (filter_index (a :: l) _ _ _ H1) as [j' [Hj' Hjj']].
     simpl in H0, H1. rewrite Hfa in H0, H1.
     destruct i.
     + destruct j; [lia | ].
       simpl in H0. inversion H0. subst a. clear H0.
       simpl in H1. exists 0.
       destruct j'; [lia | ].
       exists (S j'). repeat split. lia. assumption. 
     + destruct j; [lia | ].
       simpl in H0, H1.
       destruct (IHl x y i j ltac:(lia) H0 H1) as [i'' [j'' [Hij [Hi'' Hj'']]]].
       exists (S i''). exists (S j''). repeat split.
       lia. assumption. assumption.
   - intros.
     simpl in H0, H1. rewrite Hfa in H0, H1.
     destruct (IHl x y i j ltac:(lia) H0 H1) as [i'' [j'' [Hij [Hi'' Hj'']]]].
     exists (S i''). exists (S j''). repeat split.
     lia. assumption. assumption.
 Qed.

(* list_2_ind *)

Fixpoint list_2_ind {A : Type} (P : list A -> Prop)
  (I0 : P [])
  (I1 : forall x, P [x])
  (I2 : forall x y l, P l -> P (x :: y :: l)) (l : list A) : P l :=
match l with
| [] => I0
| [x] => I1 x
| x :: y :: l => I2 x y l (list_2_ind P I0 I1 I2 l)
end.

Lemma rev_list_2_ind {A : Type} (P : list A -> Prop) :
  P []
  -> (forall x, P [x])
  -> (forall x y l, P l -> P (l ++ [x; y]))
  -> forall l, P l.
Proof.
  intros I0 I1 I2 l.
  remember (rev l) as l'.
  generalize dependent l.
  induction l' using list_2_ind; intros.
  - rewrite <- rev_involutive.
    rewrite <- Heql'. 
    apply I0.
  - rewrite <- rev_involutive.
    rewrite <- Heql'. 
    apply I1.
  - rewrite <- rev_involutive.
    rewrite <- Heql'.
    simpl. rewrite <- app_assoc.
    simpl.
    apply I2.
    apply IHl'.
    auto using rev_involutive.
Qed.

(* InConsecutive *)

Fixpoint InConsecutive {X : Type} (x1 x2 : X) (l : list X) : Prop :=
    match l with
    | [] => False
    | x :: l => match l with
        | [] => False
        | y :: l' => x = x1 /\ y = x2 \/ InConsecutive x1 x2 l
        end
    end.

Lemma in_consecutive_nil {X : Type} : forall (x1 x2 : X),
    ~ InConsecutive x1 x2 [].
Proof. auto. Qed.

Lemma in_consecutive_singleton {X : Type} : forall (x1 x2 x : X),
    ~ InConsecutive x1 x2 [x].
Proof. auto. Qed.

Lemma in_consecutive_begin {X : Type} : forall (x1 x2 : X) (l : list X),
    InConsecutive x1 x2 (x1 :: x2 :: l).
Proof. intros. simpl. auto. Qed.

Lemma in_consecutive_begin_iff {X : Type} : forall (x1 x2 a1 a2: X) (l : list X),
    InConsecutive x1 x2 (a1 :: a2 :: l) <-> x1 = a1 /\ x2 = a2 \/ InConsecutive x1 x2 (a2 :: l).
Proof.
split; simpl InConsecutive in *; intros; firstorder.
Qed.


Lemma in_consecutive_cons {X : Type} : forall (x1 x2 x : X) (l : list X),
    InConsecutive x1 x2 l -> InConsecutive x1 x2 (x :: l).
Proof.
  intros.
  simpl. destruct l.
  - now apply in_consecutive_nil in H.
  - auto.
Qed. 

Lemma in_consecutive_end {X : Type} : forall (x1 x2 : X) (l : list X),
    InConsecutive x1 x2 (l ++ [x1; x2]).
Proof.
  induction l.
  - simpl. auto.
  - simpl app. apply in_consecutive_cons. apply IHl.
Qed.

Lemma in_consecutive_end_iff {X : Type} : forall (x1 x2 a1 a2: X) (l : list X),
    InConsecutive x1 x2 (l ++ [a1; a2]) 
    <-> InConsecutive x1 x2 (l ++ [a1]) 
    \/ x1 = a1 /\ x2 = a2.
Proof.
  induction l.
  - simpl. firstorder.
  - destruct l.
    + simpl. firstorder.
    + simpl app.
      rewrite in_consecutive_begin_iff. 
      rewrite IHl. rewrite in_consecutive_begin_iff.
      simpl app. tauto.
Qed.

Lemma in_consecutive_In {X : Type} : forall (x1 x2 : X) (l : list X),
    InConsecutive x1 x2 l -> In x1 l /\ In x2 l.
Proof.
    intros. induction l.
    - simpl in H. contradiction.
    - simpl in H. destruct l.
        + simpl in H. contradiction.
        + destruct H as [[H1 H2] | H3].
            * subst. split; simpl; auto.
            * apply IHl in H3. destruct H3. split; simpl; auto.
Qed.

Lemma in_consecutive_app {X : Type} : forall (x1 x2 a1 a2: X) (l1 l2 : list X),
  InConsecutive x1 x2 (l1 ++ a1 :: a2 :: l2) 
  <-> InConsecutive x1 x2 (l1 ++ [a1])
  \/  InConsecutive x1 x2 (a2 :: l2)
  \/  x1 = a1 /\ x2 = a2.
Proof.
  intros.
  revert l1 x1 x2 a1 a2.
  induction l2.
  - intros. rewrite in_consecutive_end_iff.
    simpl. tauto.
  - intros. 
    replace (l1 ++ a1 :: a2 :: a :: l2)
      with ((l1 ++ [a1]) ++ a2 :: a :: l2) 
      by now rewrite <- app_assoc.
    rewrite IHl2.
    rewrite <- app_assoc. simpl app.
    rewrite in_consecutive_end_iff.
    rewrite in_consecutive_begin_iff.
    tauto.
Qed.

Lemma in_consecutive_rev {X : Type} : forall (x1 x2 : X) (l : list X),
  InConsecutive x1 x2 (rev l) <-> InConsecutive x2 x1 l.
Proof.
  induction l.
  - simpl. tauto.
  - destruct l.
    + simpl. tauto.
    + simpl rev. rewrite <- app_assoc. 
      simpl app.
      rewrite in_consecutive_end_iff.
      replace (rev l ++ [x]) with (rev (x :: l)) by auto.
      rewrite IHl.
      rewrite in_consecutive_begin_iff.
      tauto.
Qed.

Lemma in_consecutive_map {X Y : Type} : forall (x1 x2 : X) (f : X -> Y) (l : list X),
  InConsecutive x1 x2 l -> InConsecutive (f x1) (f x2) (map f l).
Proof.
  intros. induction l.
  - simpl in H. contradiction.
  - simpl in H. destruct l.
    + simpl in H. contradiction.
    + destruct H as [[H1 H2] | H3].
      * subst. simpl. left. split; auto.
      * simpl. right. apply IHl. auto.
Qed.

Lemma in_consecutive_map_iff {X Y : Type} : forall (y1 y2 : Y) (f : X -> Y) (l : list X),
  InConsecutive y1 y2 (map f l) <-> exists x1 x2, InConsecutive x1 x2 l /\ y1 = f x1 /\ y2 = f x2.
Proof.
  intros. split; intros.
  - induction l.
    + simpl in H. contradiction.
    + simpl in H. destruct l.
      * simpl in H. contradiction.
      * destruct H as [[H1 H2] | H3].
        -- subst. exists a, x. simpl. split; auto.
        -- apply IHl in H3. destruct H3 as [x1 [x2 [H3 [H4 H5]]]].
           exists x1, x2. simpl. split; auto.
  - destruct H as [x1 [x2 [H1 [H2 H3]]]].
    subst. apply in_consecutive_map. auto.
Qed.

(* is_prefix_of *)

Definition is_prefix_of {A : Type} (w1 w2 : list A) : Prop :=
  exists w, w1 ++ w = w2.

Notation "w1 ⊑ w2" := (is_prefix_of w1 w2) (at level 70).

Lemma prefix_refl {A : Type} : forall (w : list A), w ⊑ w.
Proof.
  intros. exists []. 
  autorewrite with list.
  reflexivity.
Qed.

Lemma prefix_trans {A : Type} : forall (w1 w2 w3 : list A),
  w1 ⊑ w2
  -> w2 ⊑ w3
  -> w1 ⊑ w3.
Proof.
  intros.
  destruct H as [w4 Hw4].
  destruct H0 as [w5 Hw5].
  exists (w4 ++ w5).
  rewrite app_assoc.
  rewrite Hw4, Hw5.
  reflexivity.
Qed.

Lemma prefix_app {A : Type} : forall (w1 w2 w3 : list A),
  w1 ⊑ w2
  -> w1 ⊑ w2 ++ w3.
Proof.
  intros.
  destruct H as [w4 Hw4].
  exists (w4 ++ w3).
  rewrite app_assoc. rewrite Hw4.
  reflexivity.
Qed.

Lemma prefix_antisym {A : Type} : forall (w1 w2 : list A),
  w1 ⊑ w2
  -> w2 ⊑ w1
  -> w1 = w2.
Proof.
  intros.
  destruct H as [w3 Hw3].
  destruct H0 as [w4 Hw4].
  rewrite <- Hw3 in Hw4.
  rewrite <- app_assoc in Hw4.
  replace w1 with (w1 ++ []) in Hw4 at 2 by now rewrite app_nil_r.
  apply app_inv_head in Hw4.
  destruct w3; destruct w4; inversion Hw4.
  rewrite app_nil_r in Hw3.
  apply Hw3.
Qed.

Lemma prefix_firstn {A : Type} : forall (w : list A) (n : nat),
  firstn n w ⊑ w.
Proof.
  intros.
  exists (skipn n w).
  rewrite firstn_skipn.
  reflexivity.
Qed.

Lemma prefix_eq_length {A : Type} (x1 x2 w : list A) :
  x1 ⊑ w
  -> x2 ⊑ w
  -> length x1 = length x2
  -> x1 = x2.
Proof.
  intros.
  unfold is_prefix_of in *.
  remember (length x1) as n.
  revert Heqn.
  revert H H0 H1.
  revert x1 x2 w.
  induction n.
  - intros. 
    assert (x1 = []) by now apply length_zero_iff_nil.
    assert (x2 = []) by now apply length_zero_iff_nil.
    subst. reflexivity.
  - intros.
    destruct x1; [ inversion Heqn | ].
    destruct x2; [ inversion H1 | ].
    destruct H as [w1 Hw1].
    destruct H0 as [w2 Hw2].
    simpl in Hw1, Hw2.
    assert (a = a0).
    { rewrite <- Hw1 in Hw2. now inversion Hw2. }
    subst a0.
    f_equal.
   destruct w.
   { inversion Hw1. }
   assert (a = a0) by now inversion Hw1.
   subst a0.
   specialize (IHn x1 x2 w).
   assert (exists w0, x1 ++ w0 = w).
   { exists w1. now inversion Hw1. }
    assert (exists w0, x2 ++ w0 = w).
    { exists w2. now inversion Hw2. }
  simpl in H1, Heqn.
  exact (IHn H H0 ltac:(lia) ltac:(lia)). 
Qed.

Lemma prefix_firstn_iff {A : Type} (x w : list A) :
  x ⊑ w
  <-> x = firstn (length x) w.
Proof.
  split. {
  intros.
  pose proof (prefix_firstn w (length x)).
  assert (length x <= length w).
  { destruct H as [w' Hw'].
    rewrite <- Hw'. rewrite app_length.
    lia.
  }
  pose proof (firstn_length (length x) w).
  exact (prefix_eq_length x (firstn (length x) w) w H H0 ltac:(lia)).
  } {
  intros. rewrite H. apply prefix_firstn.
  }
Qed.


Lemma prefix_comparable {A : Type} : forall (x1 x2 w : list A),
  x1 ⊑ w
  -> x2 ⊑ w
  -> x1 ⊑ x2 \/ x2 ⊑ x1.
Proof.
  setoid_rewrite prefix_firstn_iff.
  intros x1 x2 w Hx1 Hx2.
  assert (length x1 <= length w). {
    rewrite Hx1.
    rewrite firstn_length.
    lia.
  }
  assert (length x2 <= length w). {
    rewrite Hx2.
    rewrite firstn_length.
    lia.
  }
  destruct (Nat.le_gt_cases (length x1) (length x2)).
  - left. 
  rewrite Hx1. rewrite Hx2.
  rewrite firstn_firstn. rewrite firstn_length.
  f_equal. lia.
  - right.
  rewrite Hx1. rewrite Hx2.
  rewrite firstn_firstn. rewrite firstn_length. 
  f_equal. lia.
Qed.

Lemma prefix_left_app {A : Type} : forall (x1 x2 w : list A),
  x1 ⊑ x2
  -> w ++ x1 ⊑ w ++ x2.
Proof.
  unfold is_prefix_of.
  intros x1 x2 w [w' Hw'].
  exists w'.
  rewrite <- app_assoc.
  rewrite Hw'.
  reflexivity.
Qed.

(* is_suffix_of *)

Definition is_suffix_of {A : Type} (w1 w2 : list A) : Prop :=
  exists w, w ++ w1 = w2.

Lemma is_suffix_is_prefix_rev {A : Type} : forall (w1 w2 : list A),
  is_suffix_of w1 w2 <-> is_prefix_of (rev w1) (rev w2).
Proof.
  unfold is_suffix_of, is_prefix_of.
  split; intros.
  - destruct H as [w Hw].
    exists (rev w).
    rewrite <- rev_app_distr.
    now rewrite Hw.
  - destruct H as [w Hw].
    exists (rev w).
    replace w with (rev (rev w)) in Hw by now rewrite rev_involutive.
    rewrite <- rev_app_distr in Hw.
    assert ( rev (rev (rev w ++ w1)) = rev (rev w2) ) by now rewrite Hw.
    repeat rewrite rev_involutive in H.
    assumption.
Qed.

Lemma suffix_refl {A : Type} : forall (w : list A), is_suffix_of w w.
Proof.
  intros. exists []. 
  autorewrite with list.
  reflexivity.
Qed.

Lemma suffix_trans {A : Type} : forall (w1 w2 w3 : list A),
  is_suffix_of w1 w2
  -> is_suffix_of w2 w3
  -> is_suffix_of w1 w3.
Proof.
  intros.
  rewrite is_suffix_is_prefix_rev in *.
  eapply prefix_trans; eauto.
Qed.

Lemma suffix_app {A : Type} : forall (w1 w2 w : list A),
  is_suffix_of w1 w2
  -> is_suffix_of w1 (w ++ w2).
Proof.
  intros.
  rewrite is_suffix_is_prefix_rev in *.
  rewrite rev_app_distr.
  eapply prefix_app; eauto.
Qed.

Lemma suffix_antisym {A : Type} : forall (w1 w2 : list A),
  is_suffix_of w1 w2
  -> is_suffix_of w2 w1
  -> w1 = w2.
Proof.
  intros.
  rewrite is_suffix_is_prefix_rev in *.
  assert (rev w1 = rev w2) by now eapply prefix_antisym; eauto.
  assert (rev (rev w1) = rev (rev w2)) by now rewrite H1.
  repeat rewrite rev_involutive in H2.
  assumption.
Qed.

Lemma suffix_firstn {A : Type} : forall (w : list A) (n : nat),
  is_suffix_of (skipn n w) w.
Proof.
  intros.
  unfold is_suffix_of.
  exists (firstn n w).
  now rewrite firstn_skipn.
Qed.

Lemma suffix_eq_length {A : Type} (x1 x2 w : list A) :
  is_suffix_of x1 w
  -> is_suffix_of x2 w
  -> length x1 = length x2
  -> x1 = x2.
Proof.
  intros.
  rewrite is_suffix_is_prefix_rev in *.
  assert (rev x1 = rev x2). {
    eapply prefix_eq_length; eauto.
    now repeat rewrite rev_length.
  }
  assert (rev (rev x1) = rev (rev x2)) by now rewrite H2.
  now repeat rewrite rev_involutive in H3.
Qed.

Lemma suffix_skipn_iff {A : Type} (x w : list A) :
  is_suffix_of x w
  <-> x = skipn (length w - length x) w.
Proof.
  split.
  - intros.
    assert (length w >= length x) as Hl. {
      destruct H as [w' Hw'].
      rewrite <- Hw'.
      rewrite app_length.
      lia.
    }
    rewrite is_suffix_is_prefix_rev in H.
    rewrite prefix_firstn_iff in H.
    remember (rev w) as w'.
    rewrite rev_length in H.
    replace (length x) with (length w - (length w - length x)) in H by lia.
    assert (rev (rev x) = rev (firstn (length w - (length w - length x)) w')) by now rewrite H.
    assert ((length w) = (length w')).
    { rewrite Heqw'. now rewrite rev_length. }
    rewrite H1 in H0 at 1.
    rewrite <- skipn_rev in H0.
    subst w'.
    now repeat rewrite rev_involutive in H0.
  - intros. rewrite H.
    apply suffix_firstn. 
Qed.

Lemma suffix_comparable {A : Type} : forall (x1 x2 w : list A),
  is_suffix_of x1 w
  -> is_suffix_of x2 w
  -> is_suffix_of x1 x2 \/ is_suffix_of x2 x1.
Proof.
  intros.
  repeat rewrite is_suffix_is_prefix_rev in *.
  eapply prefix_comparable; eauto.
Qed.

Lemma suffix_right_app {A : Type} : forall (x1 x2 w : list A),
  is_suffix_of x1 x2
  -> is_suffix_of (x1 ++ w) (x2 ++ w).
Proof.
  intros.
  rewrite is_suffix_is_prefix_rev in *.
  repeat rewrite rev_app_distr.
  apply prefix_left_app; auto.
Qed.


(* is_first_member *)

Definition is_first_member {X : Type} (x : X) (l : list X) (P : X -> Prop) : Prop :=
  exists i,
    nth_error l i = Some x
    /\ P x
    /\ forall j y,
         j < i
      -> nth_error l j = Some y
      -> ~ P y.

Lemma is_first_member_unique {X : Type} (x y : X) (l : list X) (P : X -> Prop) :
  is_first_member x l P
  -> is_first_member y l P
  -> x = y.
Proof.
  unfold is_first_member.
  intros Hx Hy.
  destruct Hx as [i [Hxi [HxP Hx]]].
  destruct Hy as [j [Hyi [HyP Hy]]].
  destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hij]].
  - specialize (Hy _ _ Hij Hxi). contradiction.
  - congruence.
  - specialize (Hx _ _ Hij Hyi). contradiction.
Qed.

Lemma is_first_member_exists {X : Type} (l : list X) (P : X -> Prop) (decP : forall x, {P x} + {~ P x}) :
  forall x,
    In x l
    -> P x
    -> exists x', is_first_member x' l P.
Proof.
  induction l. {
  intros x Hin Hx.
  inversion Hin. }
  { intros x Hin Hx.
  destruct (decP a) as [Ha | Ha].
  - exists a. exists 0. simpl. repeat split; try assumption.
    intros. inversion H.
  - assert (In x l /\ P x).
  { simpl in Hin. 
    destruct Hin as [Hin | Hin].
    - subst. contradiction.
    - split; assumption. 
  }
  specialize (IHl x ltac:(tauto) ltac:(tauto)).
  destruct IHl as [x' [i [Hxi [Hx'P Hx']]]].
  exists x'. exists (S i). simpl. 
  repeat split; try assumption.  
  intros j y Hji Hyj.
  destruct j.
  + simpl in Hyj. inversion Hyj.
    subst. assumption.
  + simpl in Hyj. eapply Hx'.
    2 : eauto. 
    lia.  
  }
Qed.

Lemma is_first_member_cons {X : Type} (x1 x2 : X) (l : list X) (P : X -> Prop) :
  is_first_member x1 (x2 :: l) P
  <-> (x1 = x2 /\ P x1
  \/ (~ P x2 /\ is_first_member x1 l P)).
Proof.
  unfold is_first_member.
  split; intros.
  - destruct H as [i [Hxi [HxP Hx]]].
    destruct i.
    + simpl in Hxi. inversion Hxi. subst. auto.
    + simpl in Hxi.
      right. split. 
      * eapply Hx. apply Nat.lt_0_succ.
        reflexivity.
      * exists i. repeat split; try assumption.
      intros. apply Hx with (j := S j). lia. auto.
  - destruct H as [[Hx1 Hx1P] | Hx1].
    + subst. exists 0. simpl. repeat split; try assumption.
      intros. inversion H.
    + destruct Hx1 as [Hx2P Hx1].
      destruct Hx1 as [i [Hxi [Hx1P Hx1]]].
      exists (S i). simpl. repeat split; try assumption.
      intros. destruct j.
      * simpl in H0. inversion H0. subst. assumption.
      * simpl in H0. apply Hx1 with (j := j). lia. assumption.
Qed.


Lemma find_some_first_member {X : Type} (l : list X) (pred : X -> bool) :
  forall x,
    find pred l = Some x
    <-> is_first_member x l (fun x => pred x = true).
Proof.
  induction l; intros.
  - simpl. unfold is_first_member. split.
    + discriminate.
    + intros [i [H _]]. destruct i; inversion H.
  - rewrite is_first_member_cons. simpl.
    rewrite <- IHl.
    destruct (pred a) eqn:Ha.
    + split; intros.
      * inversion H. subst.
        auto.
      * destruct H as [[Hx1 Hx1P] | Hx1].
        subst. auto.
        destruct Hx1 as [Hx2P Hx1].
        congruence.
    + firstorder. subst. congruence.
Qed.

Lemma find_none_first_member {X : Type} (l : list X) (pred : X -> bool) :
  find pred l = None
  <-> forall x, ~ is_first_member x l (fun x => pred x = true).
Proof.
  split.
  - intros Hnone x Hx.
    rewrite <- find_some_first_member in Hx.
    congruence.
  - intros.
    destruct (find pred l) eqn:Hfind; [ | auto].
    rewrite find_some_first_member in Hfind.
    firstorder.
Qed.

(* window_agree *)

Definition window_agree {A : Type} (start delta : nat) (w1 w2 : list A) :=
  forall i, i < delta -> nth_error w1 (start + i) = nth_error w2 (start + i).

Definition window_agree_2 {A : Type} (start1 start2 delta : nat) (w1 w2 : list A) :=
  forall i, i < delta -> nth_error w1 (start1 + i) = nth_error w2 (start2 + i).

Lemma window_agree_symm {A : Type} : forall (start delta : nat) (w1 w2 : list A),
  window_agree start delta w1 w2
  -> window_agree start delta w2 w1.
Proof.
  unfold window_agree.
  intros. firstorder.
Qed.

Lemma window_agree_2_comm {A : Type} : forall (start1 start2 delta : nat) (w1 w2 : list A),
  window_agree_2 start1 start2 delta w1 w2
  -> window_agree_2 start2 start1 delta w2 w1.
Proof.
  unfold window_agree_2.
  intros. firstorder.
Qed.

Lemma window_agree_agree_2 {A : Type} : forall (start delta : nat) (w1 w2 : list A),
  window_agree start delta w1 w2
  -> window_agree_2 start start delta w1 w2.
Proof.
  unfold window_agree_2, window_agree.
  intros. auto.
Qed.

Lemma window_agree_2_agree {A : Type} : forall (start1 start2 delta : nat) (w1 w2 : list A),
  start2 >= start1
  -> window_agree_2 start1 start2 delta w1 w2
  -> window_agree start1 delta w1 (skipn (start2 - start1) w2).
Proof.
  unfold window_agree_2, window_agree.
  intros.
  rewrite <- nth_error_skipn.
  replace (start1 + i + (start2 - start1)) with (start2 + i) by lia.
  now apply H0.
Qed.

(* when the first window contains the second window, then the second window agrees automatically *)
Lemma window_agree_smaller {A : Type} : forall (start delta : nat) (w1 w2 : list A),
  window_agree start delta w1 w2
  -> forall start' delta',
       start' >= start
    -> start' + delta' <= start + delta
    -> window_agree start' delta' w1 w2.
Proof.
  intros.
  intros i' Hi'.
  replace (start' + i') with (start + (i' + (start' - start))) by lia.
  apply H. lia.
Qed.

Lemma window_agree_2_smaller {A : Type} : forall (start1 start2 delta : nat) (w1 w2 : list A),
  window_agree_2 start1 start2 delta w1 w2
  -> forall d' delta',
       start1 + d' + delta' <= start1 + delta
    -> start2 + d' + delta' <= start2 + delta
    -> window_agree_2 (start1 + d') (start2 + d') delta' w1 w2.
Proof.
  intros.
  intros i' Hi'.
  replace (start1 + d' + i') with (start1 + (i' + d')) by lia.
  replace (start2 + d' + i') with (start2 + (i' + d')) by lia.
  apply H. lia.
Qed.

Lemma window_agree_firstn {A : Type} (w : list A) (n : nat) :
  window_agree 0 n w (firstn n w).
Proof.
  intros.
  intros i Hi.
  simpl.
  now rewrite nth_error_firstn by assumption.
Qed.

Lemma window_agree_2_skipn {A : Type} (w : list A) (n : nat) :
  window_agree_2 n 0 (length w - n) w (skipn n w).
Proof.
  intros.
  intros i Hi.
  simpl. replace (n + i) with (i + n) by lia.
  now rewrite nth_error_skipn.
Qed.

(* seq *)

Lemma seq_nth_error : forall start len i,
  i < len
  -> nth_error (seq start len) i = Some (start + i).
Proof.
  intros start len i.
  revert start len.
  induction i; intros.
  - destruct len; [lia | ].
    simpl. auto.
  - destruct len; [lia | ].
    simpl.
    specialize (IHi (S start) len ltac:(lia)).
    rewrite IHi. f_equal. lia.
Qed.

(* altr / last_Some / opt_enum / find_largest_true *)

Definition altr {X : Type} (a b : option X) : option X :=
  match b with
  | None => a
  | _ => b
  end.

Notation "a <|>> b" := (altr a b) (at level 50).

Lemma altr_None_l {X} : forall (a : option X),
  None <|>> a = a.
Proof.
  intros. unfold altr. destruct a; auto.
Qed.

Lemma altr_None_inv {X} : forall (a b : option X),
  a <|>> b = None
  -> a = None /\ b = None.
Proof.
  intros; destruct a; destruct b; inversion H; auto.
Qed.


Lemma altr_assoc {X} : forall (a b c : option X),
  a <|>> (b <|>> c) = (a <|>> b) <|>> c.
Proof.
  intros. unfold altr. destruct a, b, c; auto.
Qed.

Definition last_Some {X} (l : list (option X)) : option X :=
  fold_right altr None l .

Lemma last_Some_foldr {X} : forall (l : list (option X)) (x : option X),
  fold_right altr x l = last_Some l <|>> x .
Proof.
  induction l.
  - intros. simpl. rewrite altr_None_l. auto.
  - intros. simpl. rewrite IHl.
    rewrite altr_assoc. auto. 
Qed.

Lemma last_Some_app {X} : forall (l1 l2 : list (option X)),
  last_Some (l1 ++ l2) = last_Some l1 <|>> last_Some l2.
Proof.
  intros. unfold last_Some. rewrite fold_right_app.
  rewrite last_Some_foldr. auto.
Qed.

Lemma last_Some_None_iff {X} : forall (l : list (option X)),
  last_Some l = None
  <-> forall x, In x l -> x = None.
Proof.
  split.
  { induction l.
  - intros. destruct H0.
  - intros. simpl in H.
    apply altr_None_inv in H as [H1 H2].
    subst a. destruct H0; auto.
  }
  { induction l.
  - auto.
  - intros. simpl.
    specialize (H a ltac:(left; auto)) as HH. subst a.
    rewrite altr_None_l. apply IHl. intros.
    apply H. right. auto.
  } 
Qed.

Lemma last_Some_nth_error {X} : forall (l : list (option X)) i,
  forall x, nth_error l i = Some (Some x)
  -> (forall j, j > i -> j < length l -> nth_error l j = Some None)
  -> last_Some l = Some x.
Proof.
  intros.
  assert (i < length l) as Li. {
    rewrite <- nth_error_Some. congruence.
  }
  pose proof (firstn_skipn (S i) l).
  remember (skipn (S i) l) as l2.
  assert (forall b, In b l2 -> b = None) as Hnone. {
    intros. subst l2.
    apply In_nth_error in H2.
    destruct H2 as [j' Hj'].
    rewrite <- nth_error_skipn in Hj'.
    assert (j' + S i < length l) as Hjlen. {
      rewrite <- nth_error_Some. congruence.
    }
    specialize (H0 (j' + S i) ltac:(lia) ltac:(lia)).
    congruence.
  }
  rewrite <- H1.
  rewrite last_Some_app.
  rewrite <- last_Some_None_iff in Hnone. rewrite Hnone.
  destruct (unsnoc (firstn (S i) l)) as [[l1 a] | ] eqn:E.
  2 : {
    apply unsnoc_None in E.
    apply f_equal with (f := @length (option X)) in E.
    rewrite firstn_length in E.
    simpl length in E. lia.
  }
  rewrite unsnoc_Some in E.
  rewrite E.
  rewrite last_Some_app. simpl.
  erewrite <- nth_error_firstn in H.
  rewrite E in H. 2 : lia.
  assert (length l1 = i) as Hl1. {
    apply f_equal with (f := @length (option X)) in E.
    rewrite firstn_length in E.
    rewrite app_length in E. simpl length in E. lia.
  }
  rewrite nth_error_app2 in H by lia.
  replace (i - length l1) with 0 in H by lia.
  simpl in H. inversion H. auto.
Qed.

Lemma last_Some_nth_error_bw {X} : forall (l : list (option X)),
  forall x, last_Some l = Some x
  -> exists i, nth_error l i = Some (Some x)
  /\ (forall j, j > i -> j < length l -> nth_error l j = Some None).
Proof.
  induction l using rev_ind.
  {
  intros. simpl in H. inversion H.
  }
  intros. destruct x as [x | ].
  {
    rewrite last_Some_app in H.
    simpl in H. inversion H. subst x0.
    exists (length l). split.
    - rewrite nth_error_app2. 2 : lia.
      replace (length l - length l) with 0 by lia.
      simpl. auto.
    - intros. rewrite app_length in H1. simpl in H1. lia.
  }
  {
    rewrite last_Some_app in H.
    simpl in H.
    specialize (IHl x0 H) as [i [Hi Hnone]].
    exists i. split.
    - rewrite nth_error_app1. auto.
      apply nth_error_Some. congruence.
    - intros. rewrite app_length in H1. simpl in H1.
      assert (j < length l \/ j = length l) as [Hj | Hj] by lia.
      + rewrite nth_error_app1. apply Hnone. lia. auto. auto.
      + subst j. rewrite nth_error_app2. 2 : lia.
        replace (length l - length l) with 0 by lia.
        simpl. auto. 
  }
Qed.

Definition opt_enum (lb : list bool) : list (option nat) :=
  zipWith (fun (b : bool) i => if b then Some i else None) lb (seq 0 (length lb)).

Lemma opt_enum_length : forall lb,
  length (opt_enum lb) = length lb.
Proof.
  intros. unfold opt_enum. rewrite zipWith_length.
  rewrite seq_length. lia.
Qed.

Lemma opt_enum_nth_error : forall lb i,
  i < length lb
  -> nth_error (opt_enum lb) i = Some (Some i)
  <-> nth_error lb i = Some true.
Proof.
  intros. unfold opt_enum.
  rewrite nth_error_zipWith.
  rewrite seq_nth_error. 2 : lia.
  simpl. rewrite nth_error_Some_ex in H.
  destruct H as [x Hx].
  rewrite Hx. split.
  - intros X. inversion X. f_equal.
    destruct x; [auto | discriminate].
  - intros X. inversion X. f_equal.
Qed.

Lemma opt_enum_nth_error_2 : forall lb i,
  i < length lb
  -> nth_error (opt_enum lb) i = Some None
  \/ nth_error (opt_enum lb) i = Some (Some i).
Proof.
  intros. unfold opt_enum.
  rewrite nth_error_zipWith.
  rewrite seq_nth_error. 2 : lia.
  simpl. rewrite nth_error_Some_ex in H.
  destruct H as [x Hx].
  destruct x.
  - right. now rewrite Hx.
  - left. now rewrite Hx.
Qed.

Lemma opt_enum_nth_error_3 : forall lb i,
  i < length lb
  -> nth_error (opt_enum lb) i = Some None
  <-> nth_error lb i = Some false.
Proof.
  intros.
  pose proof (opt_enum_length lb).
  assert (i < length (opt_enum lb)) by congruence.
  assert (Hi := H). assert (Hi' := H1).
  rewrite nth_error_Some_ex in H.
  destruct H as [x Hx].
  rewrite nth_error_Some_ex in H1.
  destruct H1 as [y Hy].
  destruct x.
  - 
    split.
    + intros. rewrite <- opt_enum_nth_error in Hx. congruence. auto.
    + intros. congruence.
  - split; intros.
    + destruct y. 
      * congruence.
      * auto.
    + destruct y.
      * pose proof (opt_enum_nth_error_2 lb i Hi) as [X | X].
        -- congruence.
        -- rewrite opt_enum_nth_error in X. 2 : auto.
           congruence.  
      * auto.
Qed.   

Lemma opt_enum_last_Some_fw : forall lb,
  forall i, nth_error lb i = Some true
  -> (forall j, j > i -> j < length lb -> nth_error lb j = Some false)
  -> last_Some (opt_enum lb) = Some i.
Proof.
  intros. eapply last_Some_nth_error.
  - rewrite opt_enum_nth_error. 
    + auto.
    + rewrite <- nth_error_Some. congruence.
  - intros. rewrite opt_enum_length in H2. 
    rewrite opt_enum_nth_error_3; [ | assumption].
    apply H0; [ | assumption]. assumption.
Qed.

Lemma opt_enum_last_Some_bw : forall lb i,
  last_Some (opt_enum lb) = Some i
  -> nth_error lb i = Some true
  /\ (forall j, j > i -> j < length lb -> nth_error lb j = Some false).
Proof.
  intros. apply last_Some_nth_error_bw in H.
  destruct H as [j [Hj Hnone]].
  assert (j < length lb) as Hjlen. {
    rewrite <- opt_enum_length. 
    rewrite <- nth_error_Some. congruence.
  }
  destruct (opt_enum_nth_error_2 lb j ltac:(lia)) as [Hj' | Hj'].
  1 : congruence.
  rewrite Hj' in Hj. inversion Hj. subst i.
  rewrite opt_enum_nth_error in Hj'. 2 : auto.
  split; [auto | ].
  intros. rewrite opt_enum_length in Hnone. 
  specialize (Hnone j0 H H0).
  rewrite opt_enum_nth_error_3 in Hnone; auto.
Qed.

Definition find_largest_true (lb : list bool) : option nat :=
  last_Some (opt_enum lb).

Lemma find_largest_true_Some : forall lb i,
  find_largest_true lb = Some i
  <-> nth_error lb i = Some true
  /\ (forall j, j > i -> j < length lb -> nth_error lb j = Some false).
Proof.
  intros. unfold find_largest_true.
  split.
  - intros. apply opt_enum_last_Some_bw in H. auto.
  - intros. destruct H as [H1 H2]. apply opt_enum_last_Some_fw; auto.
Qed.

Lemma find_largest_true_None : forall lb,
  find_largest_true lb = None
  <-> forall b, In b lb -> b = false.
Proof.
  intros. unfold find_largest_true.
  rewrite last_Some_None_iff.
  split.
  - intros. apply In_nth_error in H0.
    destruct H0 as [i Hi].
    destruct (nth_error (opt_enum lb) i) eqn:E.
    + assert (E' := E). apply nth_error_In in E. apply H in E.
      subst o. rewrite opt_enum_nth_error_3 in E'.
      * congruence.
      * apply nth_error_Some. congruence.
    + apply nth_error_None in E. rewrite opt_enum_length in E.
      pose proof (nth_error_Some lb i).
      rewrite Hi in H0. assert (Some b <> None) by discriminate.
      rewrite H0 in H1. lia.
  - intros. apply In_nth_error in H0.
    destruct H0 as [i Hi].
    destruct x. 2 : auto.
    assert (i < length lb) as Hilen. {
      replace (length lb) with (length (opt_enum lb)). 
      rewrite <- nth_error_Some. congruence.
      apply opt_enum_length.
    }
    destruct (opt_enum_nth_error_2 lb i ltac:(lia)) as [H1 | H1].
    { congruence. }
    rewrite H1 in Hi. inversion Hi. subst n.
    rewrite opt_enum_nth_error in H1. 2 : apply Hilen.
    apply nth_error_In in H1.
    specialize (H true H1). discriminate.
Qed.

Lemma find_largest_true_bounded : forall lb i,
  find_largest_true lb = Some i
  -> i < length lb.
Proof.
  intros. apply find_largest_true_Some in H.
  destruct H as [H1 H2].
  apply nth_error_Some. congruence.
Qed.