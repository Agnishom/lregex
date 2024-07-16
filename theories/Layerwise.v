(**

This file contains the main layerwise algorithm for lookahead regex matching.
  1. We will assume that we have a function [scanMatchONFA : @ORegex A -> @ostring A -> tape] that is satisfies [is_oscanMatcher].
     This means that it correctly acts as a matcher for elements of [ORegex].
  2. This file contains [absEvalAux]. This function takes a [scanMatchONFA] function, a word [w], a word [wrev] (the reverse of [w]), a length [len] (the length of the word + 1), a regex [r], an index [i], and a list of tapes [ts].
     - It returns an [ORegex], a number, and a list of tapes.
     - The [ORegex] is [abstract r]
     - The number denotes the number of queries used in [abstract r]
     - The list of tapes correspond to the valuations of the maximal lookarounds of [r].
  3. Finally, the function [scanMatch] feeds in these valuations to [scanMatchONFA] and returns a tape that is a match for [r] on [w].
  4. The main correctness theorem is [scanMatch_correct].

*)

Require Import Lia.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import LRegex.
Require Import ORegex.
Require Import Reverse.
Require Import OReverse.
Require Import Abstraction.
Require Import ListLemmas.
Require Import CMatcher.
Require Import Equations.

Section Layerwise.

Context {A : Type}.

Fixpoint absEvalAux (scanMatch : @ORegex A -> @ostring A -> tape) (w wrev : list A) (len : nat) (r : @LRegex A) (i : nat) (ts : list tape) :
  @ORegex A * nat * list tape :=
  match r with
  | Epsilon => (OEpsilon, 0, ts)
  | CharClass p => (OCharClass p, 0, ts)
  | Concat r1 r2 =>
    match absEvalAux scanMatch w wrev len r1 i ts with
    | (o1, n1, ts') => 
      match absEvalAux scanMatch w wrev len r2 (i + n1) ts' with
      | (o2, n2, ts'') => (OConcat o1 o2, n1 + n2, ts'')
      end
    end
  | Union r1 r2 =>
    match absEvalAux scanMatch w wrev len r1 i ts with
    | (o1, n1, ts') => 
      match absEvalAux scanMatch w wrev len r2 (i + n1) ts' with
      | (o2, n2, ts'') => (OUnion o1 o2, n1 + n2, ts'')
      end
    end
  | Star r =>
    match absEvalAux scanMatch w wrev len r i ts with
    | (o, n, ts') => (OStar o, n, ts')
    end
  | LookBehind r =>
    match absEvalAux scanMatch w wrev len r 0 [] with
    | (o, _, ts_inner) => 
      let vs := transpose len (rev ts_inner) in
      let newtape := scanMatch o (w, vs) in
      (OQueryPos i, 1, newtape :: ts)
    end
  | NegLookBehind r =>
    match absEvalAux scanMatch w wrev len r 0 [] with
    | (o, _, ts_inner) => 
      let vs := transpose len (rev ts_inner) in
      let newtape := scanMatch o (w, vs) in
      (OQueryNeg i, 1, newtape :: ts)
    end
  | LookAhead r =>
    match absEvalAux scanMatch w wrev len r 0 [] with
    | (o, _, ts_inner) => 
      let vs := transpose len (rev ts_inner) in
      let newtape := rev (scanMatch (oreverse o) (wrev, rev vs)) in
      (OQueryPos i, 1, newtape :: ts)
    end
  | NegLookAhead r =>
    match absEvalAux scanMatch w wrev len r 0 [] with
    | (o, _, ts_inner) => 
      let vs := transpose len (rev ts_inner) in
      let newtape := rev (scanMatch (oreverse o) (wrev, rev vs)) in
      (OQueryNeg i, 1, newtape :: ts)
    end
  end.

Definition is_otape (r : ORegex) (os : @ostring A) (t : tape) : Prop :=
  (length t = olength os + 1) /\
  forall i,
      i <= olength os ->
      (nth_error t i = Some true <-> match_oregex r (ofirstn i os)) /\
      (nth_error t i = Some false <-> ~ match_oregex r (ofirstn i os)).

Definition is_otape_slice (r : ORegex) (os : @ostring A) (t : tape) (start delta : nat) : Prop :=
  start + delta <= olength os /\
  (length t = delta + 1) /\
  forall i,
      i <= delta ->
      (nth_error t i = Some true <-> match_oregex r (ofirstn i (oskipn start os))) /\
      (nth_error t i = Some false <-> ~ match_oregex r (ofirstn i (oskipn start os))).

Lemma is_otape_oval (r : @LRegex A) (w : list A) (vs : list valuation) (t : tape) :
  is_oval r w vs
  -> is_otape (abstract r) (w, vs) t
  -> is_tape r w t.
Proof.
  intros. unfold is_tape.
  unfold is_otape in H0.
  destruct H0 as [Hlen H1].
  unfold olength in Hlen. simpl in Hlen.
  split; auto. intros d Hd.
  apply oracle_compose with (i := d) in H. 2 : { auto. }
  specialize (H1 d). unfold olength in H1.
  specialize (H1 ltac:(auto)).
  destruct H1 as [H1 H2].
  split; tauto.
Qed. 

Lemma is_otape_oval_slice (r : @LRegex A) (w : list A) (vs : list valuation) (t : tape) (start delta : nat) :
  is_oval r w vs
  -> is_otape_slice (abstract r) (w, vs) t start delta
  -> is_tape_slice r w t start delta.
Proof.
  intros. unfold is_tape_slice.
  unfold is_otape_slice in H0.
  destruct H0 as [Hlen1 [Hlen2 H1]].
  unfold olength in Hlen1. simpl in Hlen1.
  split; [auto | split; [auto | ]]. intros i Hi.
  apply oracle_compose_aux with (𝛼 := 0) (start := start) (delta := i) in H. 2 : { lia. }
  specialize (H1 i Hi).
  destruct H1 as [H1 H2].
  unfold abstract in H1, H2.
  split; tauto.
Qed.

Lemma is_otape_oval_rev (r : @LRegex A) (w : list A) (vs : list valuation) (t : tape) :
  is_oval r w vs
  -> is_otape (oreverse (abstract r)) (rev w, rev vs) t
  -> is_tape (reverse r) (rev w) t.
Proof.
  intros. unfold is_tape.
  unfold is_otape in H0.
  destruct H0 as [Hlen H1].
  unfold olength in Hlen. simpl in Hlen.
  split; auto. intros d Hd. rewrite rev_length in Hd.
  unfold olength in H1. simpl in H1.
  rewrite rev_length in H1.
  assert (outer_length_wf (w, vs)) as Hwvs. {
    unfold is_oval in H.
    apply wf_oval in H.
    firstorder.
  }
  split; split; intros.
  - replace 0 with (length w - (((length w) - d) + d)) by lia.
    rewrite <- reverse_match by lia. 
    apply oracle_compose_aux 
      with (𝛼 := 0) (start := length w - d) (delta := d) 
      in H. 2 : { lia. }
    apply <- H.
    rewrite oreverse_match_iff.
    specialize (H1 d Hd).
    apply H1 in H0.
    replace (rev w, rev vs) with (orev (w, vs)) in H0 by reflexivity.
    rewrite ofirstn_orev in H0.
    rewrite ofirstn_all2. auto.
    + apply oskipn_outer_length_wf. auto.
    + rewrite oskipn_olength. unfold olength. simpl. lia.
    + auto.
    + apply ofirstn_outer_length_wf. apply oskipn_outer_length_wf.
      auto.  
  - replace 0 with (length w - (((length w) - d) + d)) in H0 by lia.
    rewrite <- reverse_match in H0 by lia. 
    apply oracle_compose_aux 
      with (𝛼 := 0) (start := length w - d) (delta := d) 
      in H. 2 : { lia. }
    apply H in H0.
    rewrite oreverse_match_iff in H0.
    specialize (H1 d Hd).
    apply H1.
    replace (rev w, rev vs) with (orev (w, vs)) by reflexivity.
    rewrite ofirstn_orev.
    rewrite ofirstn_all2 in H0. auto.
    + apply oskipn_outer_length_wf. auto.
    + rewrite oskipn_olength. unfold olength. simpl. lia.
    + auto.
    + apply ofirstn_outer_length_wf. apply oskipn_outer_length_wf.
      auto.
  - replace 0 with (length w - (((length w) - d) + d)) by lia.
    rewrite <- reverse_match by lia. 
    apply oracle_compose_aux 
      with (𝛼 := 0) (start := length w - d) (delta := d) 
      in H. 2 : { lia. }
    rewrite H.
    rewrite oreverse_match_iff.
    specialize (H1 d Hd).
    apply H1 in H0.
    replace (rev w, rev vs) with (orev (w, vs)) in H0 by reflexivity.
    rewrite ofirstn_orev in H0.
    rewrite ofirstn_all2. auto.
    + apply oskipn_outer_length_wf. auto.
    + rewrite oskipn_olength. unfold olength. simpl. lia.
    + auto.
    + apply ofirstn_outer_length_wf. apply oskipn_outer_length_wf.
      auto.
  - replace 0 with (length w - (((length w) - d) + d)) in H0 by lia.
    rewrite <- reverse_match in H0 by lia. 
    apply oracle_compose_aux 
      with (𝛼 := 0) (start := length w - d) (delta := d) 
      in H. 2 : { lia. }
    rewrite H in H0.
    rewrite oreverse_match_iff in H0.
    specialize (H1 d Hd).
    apply H1.
    replace (rev w, rev vs) with (orev (w, vs)) by reflexivity.
    rewrite ofirstn_orev.
    rewrite ofirstn_all2 in H0. auto.
    + apply oskipn_outer_length_wf. auto.
    + rewrite oskipn_olength. unfold olength. simpl. lia.
    + auto.
    + apply ofirstn_outer_length_wf. apply oskipn_outer_length_wf.
      auto.
Qed. 


Lemma arity_reverse : forall (r : @LRegex A),
  arity (reverse r) = arity r.
Proof.
  induction r; simpl; auto.
  all: unfold arity in * ; simpl; repeat rewrite app_length;
       lia.
Qed.

Definition is_oscanMatcher (oscanMatch : @ORegex A -> @ostring A -> tape) : Prop :=
  forall r os,
    outer_length_wf os
    -> is_otape r os (oscanMatch r os).

Lemma oscanMatcher_slice (oscanMatch : @ORegex A -> @ostring A -> tape) 
  (start delta : nat) (HoscanMatch : is_oscanMatcher oscanMatch): 
  forall or os,
    outer_length_wf os
    -> start + delta <= olength os
    -> is_otape_slice or os (oscanMatch or (ofirstn delta (oskipn start os))) start delta.
Proof.
  intros or os Hwf Hsd.
  remember (ofirstn delta (oskipn start os)) as oslice.
  assert (outer_length_wf oslice) as Hwf'. {
    subst.
    apply ofirstn_outer_length_wf.
    apply oskipn_outer_length_wf.
    apply Hwf.
  }
  specialize (HoscanMatch or oslice Hwf').
  unfold is_otape in HoscanMatch.
  unfold is_otape_slice.
  destruct HoscanMatch as [Hlen Htape].
  assert (olength oslice = delta) as Hlenslice. {
    subst.
    rewrite ofirstn_olength. rewrite oskipn_olength. lia.
  }
  rewrite Hlenslice in Hlen, Htape.
  split; [auto | split; [auto | ]].
  intros i Hi.
  specialize (Htape i Hi).
  assert (ofirstn i oslice = ofirstn i (oskipn start os)) as Hslsl. {
    subst.
    rewrite ofirstn_ofirstn.
    replace (min i delta) with i by lia.
    reflexivity.
  }
  rewrite Hslsl in Htape.
  apply Htape.
Qed.


Lemma absEvalAux_spec : forall (r : @LRegex A) (oscanMatch : @ORegex A -> @ostring A -> tape),
  is_oscanMatcher oscanMatch 
  -> forall (w wrev : list A), wrev = rev w 
  -> forall (len : nat), len = length w + 1
  -> forall (ts : list tape), (forall t, In t ts -> length t = len)
  -> forall (𝛼 : nat) (o : @ORegex A) (n : nat) (ts' : list tape),
    absEvalAux oscanMatch w wrev len r 𝛼 ts = (o, n, ts') 
    -> o = abstractAux 𝛼 r
    /\ n = arity r
    /\ exists (ts1 : list tape),
        ts' = ts1 ++ ts
        /\ length ts1 = arity r
        /\ (forall t, In t ts1 -> length t = len)
        /\ forall i, i < n
        -> forall lar tayp,
             nth_error (maximal_lookarounds r) i = Some lar
          -> nth_error ts1 (n - S i) = Some tayp
          -> is_lookaround_tape lar w tayp.
Proof. 
  induction r.
  - (* ε *)
    intros oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht.
    intros 𝛼 o n ts' H. 
    simpl in *.
    inversion H. clear H. subst o n.
    repeat split; auto.
    exists [].
    repeat split; auto.
    + intros. destruct H.
    + intros. lia.
  - (* CharClass *)
    intros oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht.
    intros 𝛼 o n ts' H. 
    simpl in *.
    inversion H. clear H. subst o n.
    repeat split; auto.
    exists [].
    repeat split; auto.
    + intros. destruct H.
    + intros. lia.
  - (* r1 · r2 *) 
    intros oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht.
    intros 𝛼 o n ts''' H. 
    simpl in *.
    destruct (absEvalAux oscanMatch w wrev len r1 𝛼 ts) as [[o1 n1] ts'] eqn:Hr1.
    destruct (absEvalAux oscanMatch w wrev len r2 (𝛼 + n1) ts') as [[o2 n2] ts''] eqn:Hr2.
    rewrite arity_concat.
    specialize (IHr1 oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht 𝛼 o1 n1 ts' Hr1).
    destruct IHr1 as [IHo1 [IHn1 [ts1 [Hts1 [Htslen [Hts1' Hts_tapes]]]]]].
    specialize (IHr2 oscanMatch Hoscanner w wrev Hwrev len Hlen ts').
    assert (forall t : tape, In t ts' -> length t = len) as Hts'. {
     rewrite Hts1. intro t.
     rewrite in_app_iff. intros [ | ]; auto.
    }
    specialize (IHr2 Hts' (𝛼 + n1) o2 n2 ts'' Hr2).
    destruct IHr2 as [IHo2 [IHn2 [ts2 [Hts2 [Hts2len [Hts2' Hts2_tapes]]]]]].
    inversion H. clear H. subst ts'''.
    rewrite IHn2. rewrite IHn1.
    rewrite IHo1. rewrite IHo2.
    rewrite IHn1. 
    repeat split; auto.
    exists (ts2 ++ ts1).
    repeat split.
    + rewrite Hts2. rewrite Hts1. rewrite app_assoc. auto.
    + rewrite app_length. rewrite Hts2len. rewrite Htslen. lia.
    + intros t Ht'.
      rewrite in_app_iff in Ht'.
      destruct Ht' as [Ht' | Ht'].
      * apply Hts2'. auto.
      * apply Hts1'. auto.
    + intros i Hi.
      assert (i < arity r1 \/ i >= arity r1) as [Hi1 | Hi1] by lia. {
        intros. rewrite nth_error_app1 in H. 2 : { unfold arity in *. lia. }
        rewrite nth_error_app2 in H0. 2 : { unfold arity in *. lia. }
        rewrite Hts2len in H0.
        replace (arity r1 + arity r2 - S i - arity r2) with (arity r1 - S i) in H0 by lia.
        apply Hts_tapes with (i := i). rewrite IHn1. auto.
        auto. rewrite IHn1. auto.
      } {
        intros. rewrite nth_error_app2 in H. 2 : { unfold arity in *. lia. }
        rewrite nth_error_app1 in H0. 2 : { unfold arity in *. lia. }
        replace (arity r1 + arity r2 - S i ) with (n - S i) in H0 by lia.
        apply Hts2_tapes with (i := i - arity r1). lia. 
        unfold arity. rewrite H. auto.
        replace (n2 - S (i - arity r1)) with (n - S i) by lia.
        auto.
      }
  - (* r1 ∪ r2 *)
  intros oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht.
  intros 𝛼 o n ts''' H. 
  simpl in *.
  destruct (absEvalAux oscanMatch w wrev len r1 𝛼 ts) as [[o1 n1] ts'] eqn:Hr1.
  destruct (absEvalAux oscanMatch w wrev len r2 (𝛼 + n1) ts') as [[o2 n2] ts''] eqn:Hr2.
  rewrite arity_union.
  specialize (IHr1 oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht 𝛼 o1 n1 ts' Hr1).
  destruct IHr1 as [IHo1 [IHn1 [ts1 [Hts1 [Htslen [Hts1' Hts_tapes]]]]]].
  specialize (IHr2 oscanMatch Hoscanner w wrev Hwrev len Hlen ts').
  assert (forall t : tape, In t ts' -> length t = len) as Hts'. {
   rewrite Hts1. intro t.
   rewrite in_app_iff. intros [ | ]; auto.
  }
  specialize (IHr2 Hts' (𝛼 + n1) o2 n2 ts'' Hr2).
  destruct IHr2 as [IHo2 [IHn2 [ts2 [Hts2 [Hts2len [Hts2' Hts2_tapes]]]]]].
  inversion H. clear H. subst ts'''.
  rewrite IHn2. rewrite IHn1.
  rewrite IHo1. rewrite IHo2.
  rewrite IHn1. 
  repeat split; auto.
  exists (ts2 ++ ts1).
  repeat split.
  + rewrite Hts2. rewrite Hts1. rewrite app_assoc. auto.
  + rewrite app_length. rewrite Hts2len. rewrite Htslen. lia.
  + intros t Ht'.
    rewrite in_app_iff in Ht'.
    destruct Ht' as [Ht' | Ht'].
    * apply Hts2'. auto.
    * apply Hts1'. auto.
  + intros i Hi.
    assert (i < arity r1 \/ i >= arity r1) as [Hi1 | Hi1] by lia. {
      intros. rewrite nth_error_app1 in H. 2 : { unfold arity in *. lia. }
      rewrite nth_error_app2 in H0. 2 : { unfold arity in *. lia. }
      rewrite Hts2len in H0.
      replace (arity r1 + arity r2 - S i - arity r2) with (arity r1 - S i) in H0 by lia.
      apply Hts_tapes with (i := i). rewrite IHn1. auto.
      auto. rewrite IHn1. auto.
    } {
      intros. rewrite nth_error_app2 in H. 2 : { unfold arity in *. lia. }
      rewrite nth_error_app1 in H0. 2 : { unfold arity in *. lia. }
      replace (arity r1 + arity r2 - S i ) with (n - S i) in H0 by lia.
      apply Hts2_tapes with (i := i - arity r1). lia. 
      unfold arity. rewrite H. auto.
      replace (n2 - S (i - arity r1)) with (n - S i) by lia.
      auto.
    }
  - (* r * *)
    intros oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht.
    intros 𝛼 o n ts'' H. 
    simpl in *.
    destruct (absEvalAux oscanMatch w wrev len r 𝛼 ts) as [[o1 n1] ts'] eqn:Hr1.
    inversion H. clear H. subst ts''. subst n1.
    rewrite arity_star.
    specialize (IHr oscanMatch Hoscanner w wrev Hwrev len Hlen ts Ht 𝛼 o1 n ts' Hr1).
    destruct IHr as [IHo1 [IHn1 [ts1 [Hts1 [Htslen [Hts1' Hts_tapes]]]]]].
    subst o1. repeat split; auto.
    exists ts1. repeat split; auto.
  - (* (?= r) *)
    intros oscanner Hoscanner w wrev Hwrev len Hlen ts Ht.
    intros 𝛼 o n ts' H. 
    simpl in *.
    destruct (absEvalAux oscanner w wrev len r 0 []) eqn:Hr.
    destruct p eqn: Hp.
    inversion H. clear H. rewrite arity_lookahead. subst n.
    repeat split; auto.
    exists [rev (oscanner (oreverse o0) (wrev, rev (transpose len (rev l))))].
    assert (outer_length_wf (wrev, rev (transpose len (rev l)))) as Hwf. { 
      subst wrev. unfold outer_length_wf. simpl. repeat rewrite rev_length.
      rewrite transpose_length. lia.
      intros.
      specialize (IHr oscanner Hoscanner w (rev w) ltac:(auto) len Hlen).
      specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
      destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
      enough (length t = len). lia.
      rewrite app_nil_r in Hts1.
      subst ts1. rewrite <- in_rev in H.
      now apply Ht1.
    }
    repeat split; auto.
    + simpl. intros. destruct H. 2 : { tauto. }
      unfold is_oscanMatcher in Hoscanner.
      specialize (Hoscanner (oreverse o0) (wrev, rev (transpose len (rev l))) Hwf).
      subst t. rewrite rev_length.
      unfold is_otape in Hoscanner.
      destruct Hoscanner as [Hlen' Hspec].
      unfold olength in Hlen'. simpl in Hlen'.
      rewrite Hwrev in *. rewrite rev_length in Hlen'.
      rewrite <- Hlen in Hlen'. auto.
    + intros i Hi. assert (i = 0) by lia.
      subst i. clear Hi. simpl. intros.
      inversion H. subst lar. clear H.
      inversion H0. subst tayp. clear H0.
      clear Hp. clear p.
      specialize (IHr oscanner Hoscanner w wrev Hwrev len Hlen).
      specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
      destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
      rewrite app_nil_r in Hts1.
      simpl. rewrite lookahead_tape_is_tape.
      rewrite rev_involutive.
      assert (is_oval r w (transpose len (rev l))) as Hoval. {
        unfold is_oval. unfold is_oval_aux.
        unfold oval_tapes_aux. 
        exists (rev l).
        simpl.
        repeat split.
        - subst l. rewrite rev_length. lia.
        - intro. rewrite <- in_rev. subst l. 
          rewrite <- Hlen. apply Ht1. 
        - intros. rewrite nth_error_rev in H0.
          rewrite Hts1 in H0. replace (length ts1) with n0 in H0 by congruence.
          apply Hspec with (i := i). congruence.
          auto. auto. congruence. 
        - congruence.
      }
      assert (is_otape (oreverse (abstract r)) 
              (rev w, rev (transpose len (rev l))) 
              (oscanner (oreverse o0) (rev w, rev (transpose len (rev l))))) as Hotape. {
        unfold abstract. rewrite <- Ho0.
        apply Hoscanner.
        rewrite <- Hwrev. apply Hwf.
      }
      pose proof (is_otape_oval_rev _ _ _ _ Hoval Hotape).
      congruence.
  - (* (?<= r) *)
  intros oscanner Hoscanner w wrev Hwrev len Hlen ts Ht.
  intros 𝛼 o n ts' H. 
  simpl in *.
  destruct (absEvalAux oscanner w wrev len r 0 []) eqn:Hr.
  destruct p eqn: Hp.
  inversion H. clear H. rewrite arity_lookbehind. subst n.
  repeat split; auto.
  exists [oscanner o0 (w, transpose len (rev l))].
  assert (outer_length_wf (w, transpose len (rev l))) as Hwf. { 
      subst wrev. unfold outer_length_wf. simpl.
      unfold valuation in *. rewrite transpose_length. lia.
      intros. rewrite <- in_rev in H.  
      specialize (IHr oscanner Hoscanner w (rev w) ltac:(auto) len Hlen).
      specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
      destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
      enough (length t = len). lia.
      rewrite app_nil_r in Hts1.
      subst ts1.
      now apply Ht1.
  }
  repeat split; auto.
  + simpl. intros. destruct H. 2 : { tauto. }
  unfold is_oscanMatcher in Hoscanner.
  specialize (Hoscanner o0 (w, transpose len (rev l)) Hwf).
  subst t.
  unfold is_otape in Hoscanner.
  destruct Hoscanner as [Hlen' Hspec].
  unfold olength in Hlen'. simpl in Hlen'.
  rewrite <- Hlen in Hlen'. auto.
  + intros i Hi. assert (i = 0) by lia.
  subst i. clear Hi. simpl. intros.
  inversion H. subst lar. clear H.
  inversion H0. subst tayp. clear H0.
  clear Hp. clear p.
  specialize (IHr oscanner Hoscanner w wrev Hwrev len Hlen).
  specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
  destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
  rewrite app_nil_r in Hts1.
  simpl. rewrite lookbehind_tape_is_tape.
  assert (is_oval r w (transpose len (rev l))) as Hoval. {
    unfold is_oval. unfold is_oval_aux.
    unfold oval_tapes_aux. 
    exists (rev l).
    simpl.
    repeat split.
    - subst l. rewrite rev_length. lia.
    - intro. rewrite <- in_rev. subst l. 
      rewrite <- Hlen. apply Ht1. 
    - intros. rewrite nth_error_rev in H0.
      rewrite Hts1 in H0. replace (length ts1) with n0 in H0 by congruence.
      apply Hspec with (i := i). congruence.
      auto. auto. congruence. 
    - congruence.  
  }
  assert (is_otape (abstract r) (w, transpose len (rev l)) (oscanner o0 (w, transpose len (rev l)))) as Hotape. {
    unfold abstract. rewrite <- Ho0.
    apply Hoscanner.
    apply Hwf.
  }
  pose proof (is_otape_oval _ _ _ _ Hoval Hotape) as Htape.
  apply Htape.
  - (* (?! r) *)
  intros oscanner Hoscanner w wrev Hwrev len Hlen ts Ht.
  intros 𝛼 o n ts' H. 
  simpl in *.
  destruct (absEvalAux oscanner w wrev len r 0 []) eqn:Hr.
  destruct p eqn: Hp.
  inversion H. clear H. rewrite arity_neglookahead. subst n.
  repeat split; auto.
  exists [rev (oscanner (oreverse o0) (wrev, rev (transpose len (rev l))))].
  assert (outer_length_wf (wrev, rev (transpose len (rev l)))) as Hwf. { 
    subst wrev. unfold outer_length_wf. simpl. repeat rewrite rev_length.
    rewrite transpose_length. lia.
    intros.
    specialize (IHr oscanner Hoscanner w (rev w) ltac:(auto) len Hlen).
    specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
    destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
    enough (length t = len). lia.
    rewrite app_nil_r in Hts1.
    subst ts1. rewrite <- in_rev in H.
    now apply Ht1.
  }
  repeat split; auto.
  + simpl. intros. destruct H. 2 : { tauto. }
    unfold is_oscanMatcher in Hoscanner.
    specialize (Hoscanner (oreverse o0) (wrev, rev (transpose len (rev l))) Hwf).
    subst t. rewrite rev_length.
    unfold is_otape in Hoscanner.
    destruct Hoscanner as [Hlen' Hspec].
    unfold olength in Hlen'. simpl in Hlen'.
    rewrite Hwrev in *. rewrite rev_length in Hlen'.
    rewrite <- Hlen in Hlen'. auto.
  + intros i Hi. assert (i = 0) by lia.
    subst i. clear Hi. simpl. intros.
    inversion H. subst lar. clear H.
    inversion H0. subst tayp. clear H0.
    clear Hp. clear p.
    specialize (IHr oscanner Hoscanner w wrev Hwrev len Hlen).
    specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
    destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
    rewrite app_nil_r in Hts1.
    simpl.
    rewrite lookahead_tape_is_tape.
    rewrite rev_involutive.
    assert (is_oval r w (transpose len (rev l))) as Hoval. {
      unfold is_oval. unfold is_oval_aux.
      unfold oval_tapes_aux. 
      exists (rev l).
      simpl.
      repeat split.
      - subst l. rewrite rev_length. lia.
      - intro. rewrite <- in_rev. subst l. 
        rewrite <- Hlen. apply Ht1. 
      - intros. rewrite nth_error_rev in H0.
        rewrite Hts1 in H0. replace (length ts1) with n0 in H0 by congruence.
        apply Hspec with (i := i). congruence.
        auto. auto. congruence. 
      - congruence.  
    }
    assert (is_otape (abstract r) (w, transpose len (rev l)) (oscanner o0 (w, transpose len (rev l)))) as Hotape. {
      unfold abstract. rewrite <- Ho0.
      apply Hoscanner.
      unfold outer_length_wf in Hwf |- *. 
      simpl in Hwf |- *. 
      rewrite Hwrev in Hwf. repeat rewrite rev_length in Hwf. 
      auto.
    }
    assert (is_otape (oreverse (abstract r)) 
            (rev w, rev (transpose len (rev l))) 
            (oscanner (oreverse o0) (rev w, rev (transpose len (rev l))))) as Hotape1. {
      unfold abstract. rewrite <- Ho0.
      apply Hoscanner.
      rewrite <- Hwrev. apply Hwf.
    }
    pose proof (is_otape_oval_rev _ _ _ _ Hoval Hotape1).
    congruence.
  - (* (?<! r) *)
  intros oscanner Hoscanner w wrev Hwrev len Hlen ts Ht.
  intros 𝛼 o n ts' H. 
  simpl in *.
  destruct (absEvalAux oscanner w wrev len r 0 []) eqn:Hr.
  destruct p eqn: Hp.
  inversion H. clear H. rewrite arity_neglookbehind. subst n.
  repeat split; auto.
  exists [oscanner o0 (w, transpose len (rev l))].
  assert (outer_length_wf (w, transpose len (rev l))) as Hwf. { 
      subst wrev. unfold outer_length_wf. simpl.
      unfold valuation in *. rewrite transpose_length. lia.
      intros. rewrite <- in_rev in H.  
      specialize (IHr oscanner Hoscanner w (rev w) ltac:(auto) len Hlen).
      specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
      destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
      enough (length t = len). lia.
      rewrite app_nil_r in Hts1.
      subst ts1.
      now apply Ht1.
  }
  repeat split; auto.
  + simpl. intros. destruct H. 2 : { tauto. }
  unfold is_oscanMatcher in Hoscanner.
  specialize (Hoscanner o0 (w, transpose len (rev l)) Hwf).
  subst t.
  unfold is_otape in Hoscanner.
  destruct Hoscanner as [Hlen' Hspec].
  unfold olength in Hlen'. simpl in Hlen'.
  rewrite <- Hlen in Hlen'. auto.
  + intros i Hi. assert (i = 0) by lia.
  subst i. clear Hi. simpl. intros.
  inversion H. subst lar. clear H.
  inversion H0. subst tayp. clear H0.
  clear Hp. clear p.
  specialize (IHr oscanner Hoscanner w wrev Hwrev len Hlen).
  specialize (IHr [] ltac:(simpl; tauto) 0 o0 n0 l Hr).
  destruct IHr as [Ho0 [Hn0 [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
  rewrite app_nil_r in Hts1.
  simpl. rewrite lookbehind_tape_is_tape.
  assert (is_oval r w (transpose len (rev l))) as Hoval. {
    unfold is_oval. unfold is_oval_aux.
    unfold oval_tapes_aux. 
    exists (rev l).
    simpl.
    repeat split.
    - subst l. rewrite rev_length. lia.
    - intro. rewrite <- in_rev. subst l. 
      rewrite <- Hlen. apply Ht1. 
    - intros. rewrite nth_error_rev in H0.
      rewrite Hts1 in H0. replace (length ts1) with n0 in H0 by congruence.
      apply Hspec with (i := i). congruence.
      auto. auto. congruence. 
    - congruence.  
  }
  assert (is_otape (abstract r) (w, transpose len (rev l)) (oscanner o0 (w, transpose len (rev l)))) as Hotape. {
    unfold abstract. rewrite <- Ho0.
    apply Hoscanner.
    apply Hwf.
  }
  pose proof (is_otape_oval _ _ _ _ Hoval Hotape) as Htape.
  apply Htape.
Qed.

Definition absEval (scanMatch : @ORegex A -> @ostring A -> tape) (w : list A) (r : @LRegex A) : @ORegex A * list valuation :=
  let wrev := rev w in
  let len := length w in
  match absEvalAux scanMatch w wrev (len + 1) r 0 [] with
  | (o, _, vs) => (o, transpose (len + 1) (rev vs))
  end.

Definition scanMatchWith (scanMatchONFA : @ORegex A -> @ostring A -> tape) (w : list A) (r : @LRegex A) : tape :=
  let (o, vs) := absEval scanMatchONFA w r in
  scanMatchONFA o (w, vs).

Definition scanMatchSliceWith 
  (scanMatchONFA : @ORegex A -> @ostring A -> tape)
  (w : list A) (r : @LRegex A) (start delta : nat) : tape :=
  let (o, vs) := absEval scanMatchONFA w r in
  scanMatchONFA o (ofirstn delta (oskipn start (w, vs))).

Lemma absEval_spec (scanMatch : @ORegex A -> @ostring A -> tape) (w : list A) (r : @LRegex A) :
  is_oscanMatcher scanMatch
  -> forall o vs,
  absEval scanMatch w r = (o, vs)
  -> abstract r = o /\ is_oval r w vs.
Proof.
  intros HscanMatch o vs HabsEval.
  unfold absEval in HabsEval.
  destruct (absEvalAux scanMatch w (rev w) (length w + 1) r 0 []) as [[o' n] ts] eqn:HabsEvalAux.
  inversion HabsEval. clear HabsEval. subst o'.
  pose proof (absEvalAux_spec r scanMatch HscanMatch w (rev w) 
              eq_refl (length w + 1) eq_refl [] ltac:(firstorder) 0 o n ts HabsEvalAux).
  destruct H as [Ho [Hn [ts1 [Hts1 [Hlen1 [Ht1 Hspec]]]]]].
  rewrite app_nil_r in Hts1. subst ts1.
  assert (outer_length_wf (w, transpose (length w + 1) (rev ts))) as Hwf. {
    unfold outer_length_wf. simpl. 
    unfold valuation in *.
    rewrite transpose_length. auto.
    intros. rewrite <- in_rev in H.
    apply Ht1 in H. lia.
  }
  unfold is_oval. unfold is_oval_aux.
  split; [ unfold abstract; auto | ].
  exists (rev ts). split; [ | auto].
  unfold oval_tapes_aux. simpl. repeat split.
  - rewrite rev_length. lia.
  - intro. rewrite <- in_rev. apply Ht1.
  - intros. rewrite nth_error_rev in H0.
    rewrite Hlen1 in H0. rewrite <- Hn in H0.
    apply Hspec with (i := i). congruence.
    auto. auto. congruence.
Qed.

Lemma scanMatchWith_correct : forall scanMatchONFA w r,
  is_oscanMatcher scanMatchONFA ->
  is_tape r w (scanMatchWith scanMatchONFA w r).
Proof.
  intros scanMatchONFA w r HscanMatchONFA.
  unfold scanMatchWith.
  destruct (absEval scanMatchONFA w r) as [o vs] eqn:HabsEval.
  apply absEval_spec in HabsEval. 2 : apply HscanMatchONFA.
  destruct HabsEval as [Ho Hoval].
  assert (outer_length_wf (w, vs)) as Hwf. {
    unfold is_oval in Hoval. unfold is_oval_aux in Hoval.
    destruct Hoval as [ts [Hts Hlen]].
    unfold outer_length_wf. subst. simpl.
    rewrite (@transpose_length bool). auto.
    intros t Ht. unfold oval_tapes_aux in Hts.
    destruct Hts as [Hlen' [Ht' Hspec]].
    specialize (Ht' t Ht). lia.
  }
  apply is_otape_oval with (vs := vs). 2 : { 
    unfold is_oscanMatcher in HscanMatchONFA.
    rewrite Ho.
    apply HscanMatchONFA. unfold is_oval in Hoval. apply Hwf.
  }
  apply Hoval.
Qed.

Lemma scanMatchSliceWith_correct : forall scanMatchONFA w r start delta,
  is_oscanMatcher scanMatchONFA 
  -> start + delta <= length w
  -> is_tape_slice r w (scanMatchSliceWith scanMatchONFA w r start delta) start delta.
Proof.
  intros scanMatchONFA w r start delta HscanMatchONFA Hsd.
  unfold scanMatchSliceWith.
  destruct (absEval scanMatchONFA w r) as [o vs] eqn:HabsEval.
  apply absEval_spec in HabsEval. 2 : apply HscanMatchONFA.
  destruct HabsEval as [Ho Hoval].
  assert (outer_length_wf (w, vs)) as Hwf. {
    unfold is_oval in Hoval. unfold is_oval_aux in Hoval.
    destruct Hoval as [ts [Hts Hlen]].
    unfold outer_length_wf. subst. simpl.
    rewrite (@transpose_length bool). auto.
    intros t Ht. unfold oval_tapes_aux in Hts.
    destruct Hts as [Hlen' [Ht' Hspec]].
    specialize (Ht' t Ht). lia.
  }
  apply is_otape_oval_slice with (vs := vs). 2 : {
    rewrite Ho.
    apply oscanMatcher_slice. 
    - apply HscanMatchONFA.
    - apply Hwf.
    - unfold olength; simpl; apply Hsd.
  }
  apply Hoval.
Qed.

Lemma oscanMatcher_is_oscanMatcher :
  is_oscanMatcher (@cScanMatch A).
Proof.
  unfold is_oscanMatcher. intros.
  unfold is_otape.
  pose proof (cScanMatch_tape r os).
  firstorder.
Qed.

Definition scanMatch (r : @LRegex A) (w : list A) : tape :=
  scanMatchWith (@cScanMatch A) w r.

Definition scanMatchSlice (r : @LRegex A) (w : list A) (start delta : nat) : tape :=
  scanMatchSliceWith (@cScanMatch A) w r start delta.

Lemma scanMatch_correct : forall r w,
  is_tape r w (scanMatch r w).
Proof.
  intros. 
  apply scanMatchWith_correct. 
  apply oscanMatcher_is_oscanMatcher.
Qed.

Theorem scanMatchSlice_correct : forall r w start delta,
  start + delta <= length w
  -> is_tape_slice r w (scanMatchSlice r w start delta) start delta.
Proof.
  intros. 
  apply scanMatchSliceWith_correct. 
  apply oscanMatcher_is_oscanMatcher.
  auto.
Qed.

Lemma rPass_abstract_rl (r : @LRegex A) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> forall n,
  n <= length w
  -> match_oregex (rPass (abstract r)) (ofirstn n (w, vs))
  <-> exists m, 
    m <= n
    /\ match_regex r w m (n - m).
Proof.
  intros Hwf Hoval n Hn. split. 
  + intros M.
  rewrite rPass_match in M. 2 : { apply ofirstn_outer_length_wf. auto. }
  destruct M as [m [Hm M]].
  rewrite ofirstn_olength in Hm. unfold olength in Hm. simpl in Hm.
  exists m. split.
    - lia.
    - unfold abstract in M. 
    rewrite oskipn_ofirstn_comm in M.
    2 : auto.
    2 : lia.
    rewrite <- oracle_compose_aux in M; auto.
    lia.
  + intros [m [Hm M]].
  rewrite rPass_match. 2 : { apply ofirstn_outer_length_wf. auto. }
  exists m. split.
  - rewrite ofirstn_olength. unfold olength. simpl. lia.
  - rewrite oskipn_ofirstn_comm. 2, 3: auto. 
    unfold abstract.
    rewrite <- oracle_compose_aux; auto.
    lia.
Qed.

Lemma reverse_pass_match_rl (r : @LRegex A) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> forall n d,
  d <= n <= length w
  -> match_oregex (oreverse (abstract r)) (ofirstn d (orev (ofirstn n (w, vs))))
  <-> match_regex r w (n - d) d.
Proof.
  intros Hwf Hoval n d Hnd. split.
  + intros M.
  rewrite ofirstn_orev in M.
  2 : { apply ofirstn_outer_length_wf. auto. }
  rewrite <- oreverse_match_iff in M.
  2 : { apply oskipn_outer_length_wf. apply ofirstn_outer_length_wf. auto. }
  apply <- (@oracle_compose_aux A).
  2 : lia.
  2 : apply Hoval.
  assert (olength (ofirstn n (w, vs)) = n) as Hlen. {
    rewrite ofirstn_olength. unfold olength. simpl. lia.
  }
  rewrite Hlen in M.
  rewrite oskipn_ofirstn_comm in M. 2 : auto. 2 : lia.
  replace (n - (n - d)) with d in M by lia.
  apply M.
  + intros M.
  rewrite ofirstn_orev.
  2 : { apply ofirstn_outer_length_wf. auto. }
  rewrite <- oreverse_match_iff.
  2 : { apply oskipn_outer_length_wf. apply ofirstn_outer_length_wf. auto. }
  assert (olength (ofirstn n (w, vs)) = n) as Hlen. {
    rewrite ofirstn_olength. unfold olength. simpl. lia.
  }
  rewrite Hlen.
  rewrite oskipn_ofirstn_comm. 2 : auto. 2 : lia.
  apply oracle_compose_aux.
  - apply Hoval.
  - lia.
  - replace (n - (n - d)) with d by lia.
    apply M.
Qed.

Lemma reverse_pass_match_ll (r : @LRegex A) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> forall n,
  n <= length w
  -> match_oregex (rPass (oreverse (abstract r))) (ofirstn n (orev (w, vs)))
  <-> exists d, d <= n /\ match_regex r w (length w - n) d.
Proof.
  intros Hwf Hoval n Hn.
  rewrite rPass_match.
  2 : { apply ofirstn_outer_length_wf. apply orev_outer_length_wf. auto. }
  rewrite ofirstn_olength. rewrite orev_olength. unfold olength. simpl.
  replace (min n (length w)) with n by lia.
  split.
  + intros [start [Hstart M]].
  rewrite ofirstn_orev in M. 2 : apply Hwf.
  unfold olength in M. simpl in M.
  rewrite oskipn_orev in M.
  unfold olength in M. simpl in M.
  rewrite skipn_length in M.
  replace (length w - (length w - n)) with n in M by lia.
  2 : {  apply oskipn_outer_length_wf. assumption. }
  rewrite <- oreverse_match_iff in M.
  2 : { apply ofirstn_outer_length_wf. apply oskipn_outer_length_wf. auto. }
  unfold abstract in M.
  rewrite <- oracle_compose_aux in M.
  2 : apply Hoval. 2 : lia.
  exists (n - start). split; [ lia | apply M].
  + intros [d [Hd M]].
  exists (n - d). split; [ lia | ].
  rewrite ofirstn_orev by apply Hwf.
  unfold olength. simpl.
  rewrite oskipn_orev by now apply oskipn_outer_length_wf.
  rewrite oskipn_olength. unfold olength. simpl length.
  replace (length w - (length w - n)) with n by lia.
  replace (n - (n - d)) with d by lia.
  rewrite <- oreverse_match_iff.
  2 : { apply ofirstn_outer_length_wf. apply oskipn_outer_length_wf. auto. }
  unfold abstract.
  rewrite <- oracle_compose_aux; auto.
  lia.
Qed.

Definition llmatch (r : @LRegex A) (w : list A) : option (nat * nat) :=
  (* abstraction *)
  let (or, vs) := absEval (@cScanMatch A) w r in
  (* reverse pass *)
  let bw_tape := cScanMatch (rPass (oreverse or)) (orev (w, vs)) in
  (* left-end point *)
  let lendO := find_largest_true bw_tape in
  match lendO with
  | None => None (* no left end point found *)
  | Some lend' =>
  let lend := length w - lend' in
  (* forward pass *)
  let fw_tape := cScanMatch or (oskipn lend (w, vs)) in
  (* maximum length *)
  let d := find_largest_true fw_tape in
  match d with
  | None => None (* should be impossible *)
  | Some d => Some (lend, d)
  end
  end.

Lemma reverse_pass_Some (r : @LRegex A) (or : ORegex) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> or = abstract r
  -> forall lend',
      find_largest_true (cScanMatch (rPass (oreverse or)) (orev (w, vs))) = Some lend'
  <-> ((exists d, lend' <= length w /\ (length w - lend') + d <= length w /\ match_regex r w (length w - lend') d)
   /\  (forall lend_more_left, lend_more_left < length w - lend' ->
       ~ (exists d, lend_more_left + d <= length w /\ match_regex r w lend_more_left d))).
Proof.
  intros Hwf Hoval Hor lend'.
  rewrite find_largest_true_Some.
  assert (outer_length_wf (orev (w, vs))) as Hwf' by
    now apply orev_outer_length_wf.
  pose proof (cScanMatch_tape (rPass (oreverse or)) (orev (w, vs)) Hwf') as [Hlen Htape].
  rewrite orev_olength in Hlen. unfold olength in Hlen. simpl length at 2 in Hlen.
  rewrite Hlen.
  split.
  - intros [H1 H2].
  assert (lend' <= length w) as Hlendlen. {
    enough (lend' < length w + 1) by lia.
    rewrite <- Hlen.
    apply nth_error_Some. congruence.
  }
  rewrite orev_olength in Htape. unfold olength in Htape. simpl length in Htape.
  split.
  + specialize (Htape lend' Hlendlen) as [Hlend1 Hlend2].
    rewrite Hlend1 in H1. subst or.
    rewrite reverse_pass_match_ll in H1; auto.
    destruct H1 as [d [Hd M]].
    exists d. split; [lia | split; [lia | auto ]].
  + intros lend_more_left Hlend_more_left.
    specialize (H2 (length w - lend_more_left) ltac:(lia) ltac:(lia)).
    intros M.
    assert (exists d, d <= (length w - lend_more_left) 
      /\ match_regex r w (length w - (length w - lend_more_left)) d) as M'. {
      destruct M as [d [Hd M]].
      exists d. split; [lia | ].
      replace (length w - (length w - lend_more_left)) with lend_more_left by lia.
      apply M.
    }
    rewrite <- reverse_pass_match_ll in M'.
    2 : apply Hwf. 2 : apply Hoval. 2 : lia.
    specialize (Htape (length w - lend_more_left) ltac:(lia)) as [Hlend1 _].
    subst or.
    rewrite <- Hlend1 in M'. congruence.
  - intros [H1 H2].
  rewrite orev_olength in Htape. unfold olength in Htape. simpl length in Htape.
  assert (exists d, d <= lend' /\ match_regex r w (length w - lend') d) as M. {
    destruct H1 as [d [Hd [Hd' M]]].
    exists d. split; [lia | auto].
  }
  destruct H1 as [d [Hd1 [Hd2 M']]].
  rewrite <- reverse_pass_match_ll in M.
  2 : apply Hwf. 2 : apply Hoval. 2 : lia.
  split.
  + apply Htape. lia. subst or. auto.
  + intros lend_more_left' Hll' Xll'.
    apply Htape. lia.
    intros M''.
    subst or.
    rewrite reverse_pass_match_ll in M''; auto. 2 : lia.
    destruct M'' as [d' [Hd' M'']].
    specialize (H2 (length w - lend_more_left') ltac:(lia)).
    assert (exists d : nat, 
      length w - lend_more_left' + d <= length w 
      /\ match_regex r w (length w - lend_more_left') d) as M'''. {
    exists d'. split; [lia | auto].
    }
    congruence.
Qed.

Lemma reverse_pass_None (r : @LRegex A) (or : ORegex) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> or = abstract r
  -> find_largest_true (cScanMatch (rPass (oreverse or)) (orev (w, vs))) = None
  <-> (forall lend d, 
    lend <= lend + d <= length w
    -> ~ match_regex r w lend d).
Proof.
  intros Hwf Hoval Hor.
  rewrite find_largest_true_None.
  assert (outer_length_wf (orev (w, vs))) as Hwf' by
    now apply orev_outer_length_wf.
  pose proof (cScanMatch_tape (rPass (oreverse or)) (orev (w, vs)) Hwf') as [Hlen Htape].
  rewrite orev_olength in Hlen. unfold olength in Hlen. simpl length at 2 in Hlen.
  rewrite orev_olength in Htape. unfold olength in Htape. simpl length in Htape.
  split.
  - intros Hb lend d Hld M.
  assert (exists d, d <= length w - lend /\ match_regex r w (length w - (length w - lend)) d) as M'. {
    exists d. split; [lia | ].
    replace (length w - (length w - lend)) with lend by lia.
    apply M.
  }
  rewrite <- reverse_pass_match_ll in M'.
  2 : apply Hwf. 2 : apply Hoval. 2 : lia.
  specialize (Htape (length w - lend) ltac:(lia)) as [Hlend1 Hlend2].
  subst or.
  rewrite <- Hlend1 in M'. apply nth_error_In in M'.
  specialize (Hb _ M'). discriminate.
  - intros H b Hb.
  apply In_nth_error in Hb.
  destruct Hb as [i Hi].
  assert (i <= length w) as Hilen. {
    enough (i < length w + 1) by lia.
    rewrite <- Hlen.
    apply nth_error_Some. congruence.
  }
  specialize (Htape i Hilen) as [H1 H2].
  destruct b. 2 : auto.
  rewrite H1 in Hi. subst or.
  rewrite reverse_pass_match_ll in Hi; auto.
  destruct Hi as [d [Hd M]].
  specialize (H (length w - i) d ltac:(lia)).
  contradiction.
Qed.

Lemma forward_pass_Some (r : @LRegex A) (or : ORegex) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> or = abstract r
  -> forall lend d,
      lend <= length w
  -> find_largest_true (cScanMatch or (oskipn lend (w, vs))) = Some d
  <-> match_regex r w lend d
  /\ (forall d', d' > d -> lend + d' <= length w
      -> ~ match_regex r w lend d').
Proof.
  intros Hwf Hoval Hor lend d Hlend.
  rewrite find_largest_true_Some.
  assert (outer_length_wf (oskipn lend (w, vs))) as Hwf' by
    now apply oskipn_outer_length_wf.
  pose proof (cScanMatch_tape or (oskipn lend (w, vs)) Hwf') as [Hlen Htape].
  rewrite oskipn_olength in Hlen. unfold olength in Hlen. simpl length at 2 in Hlen.
  rewrite Hlen.
  rewrite oskipn_olength in Htape. unfold olength in Htape. simpl length in Htape.
  assert (olength (oskipn lend (w, vs)) = length w - lend) as Hlen'. {
    rewrite oskipn_olength. unfold olength. simpl length. lia.
  }
  split.
  - intros [H1 H2].
  assert (d <= length w - lend) as Hdlen. {
    enough (d < length w - lend + 1) by lia.
    rewrite <- Hlen.
    apply nth_error_Some. congruence.
  }
  split.
  + specialize (Htape d Hdlen) as [Hd1 Hd2].
    rewrite Hd1 in H1. subst or.
    unfold abstract in H1.
    rewrite <- oracle_compose_aux in H1; auto.
    lia.
  + intros d' Hd' HHd'.
  specialize (Htape d' ltac:(lia)) as [Hd'1 Hd'2].
  rewrite oracle_compose_aux; eauto.
  subst or. unfold abstract in Hd'2.
  rewrite <- Hd'2.
  now specialize (H2 d' Hd' ltac:(lia)).
  - intros [H1 H2].
  specialize (match_length r w lend d H1) as L.
  rewrite oracle_compose_aux in H1; eauto. 2 : lia.
  split.
  + specialize (Htape d ltac:(lia)) as [Hd1 Hd2].
    rewrite Hd1. subst or.
    unfold abstract.
    auto.
  + intros d' Hd' HHd'.
    specialize (Htape d' ltac:(lia)) as [Hd'1 Hd'2]. 
    rewrite Hd'2. subst or. unfold abstract.
    rewrite <- oracle_compose_aux. 2 : apply Hoval. 2 : lia.
    apply H2; auto. lia.
Qed.

Lemma forward_pass_None (r : @LRegex A) (or : ORegex) (w : list A) (vs : list valuation) :
  outer_length_wf (w, vs)
  -> is_oval r w vs
  -> or = abstract r
  -> forall lend,
      lend <= length w
  -> find_largest_true (cScanMatch or (oskipn lend (w, vs))) = None
  <-> (forall d, lend + d <= length w -> ~ match_regex r w lend d).
Proof.
  intros Hwf Hoval Hor lend Hlend.
  rewrite find_largest_true_None.
  assert (outer_length_wf (oskipn lend (w, vs))) as Hwf' by
    now apply oskipn_outer_length_wf.
  pose proof (cScanMatch_tape or (oskipn lend (w, vs)) Hwf') as [Hlen Htape].
  rewrite oskipn_olength in Hlen. unfold olength in Hlen. simpl length at 2 in Hlen.
  rewrite oskipn_olength in Htape. unfold olength in Htape. simpl length in Htape.
  split.
  - intros H d Hd.
  rewrite oracle_compose_aux. 2 : apply Hoval. 2 : apply Hd.
  subst or. unfold abstract in Htape.
  apply Htape. lia.
  remember (cScanMatch _ _) as tape.
  assert (d < length tape) as Ht by lia.
  rewrite nth_error_Some_ex in Ht.
  destruct Ht as [x Hx]. rewrite Hx.
  apply nth_error_In in Hx. apply H in Hx. now subst.
  - intros H b Hb.
  apply In_nth_error in Hb.
  destruct Hb as [i Hi].
  assert (i <= length w - lend) as Hilen. {
    enough (i < length w - lend + 1) by lia.
    rewrite <- Hlen.
    apply nth_error_Some. congruence.
  }
  destruct b. 2 : auto.
  specialize (Htape i Hilen) as [H1 H2].
  rewrite H1 in Hi. clear H1 H2. 
  subst or. unfold abstract in Hi.
  rewrite <- oracle_compose_aux in Hi; auto. 2 : lia.
  specialize (H i ltac:(lia)). 
  contradiction.
Qed.

  
Lemma llmatch_Some : forall r w n d,
  llmatch r w = Some (n, d)
  -> match_regex r w n d (* match *)
  /\ (forall n', n' < n -> ~ (exists d', n' + d' <= length w /\ match_regex r w n' d')) (* leftmost *)
  /\ (forall d', d' > d -> n + d' <= length w -> ~ match_regex r w n d') (* longest *).
Proof.
  intros.
  unfold llmatch in H.
  destruct (absEval (@cScanMatch A) w r) as [or vs] eqn:HabsEval.
  pose proof (absEval_spec (@cScanMatch A) w r (cScanMatch_tape) or vs HabsEval) as [Ho Hoval].
  assert (outer_length_wf (w, vs)) as Hwf. {
    unfold is_oval in Hoval. unfold is_oval_aux in Hoval.
    destruct Hoval as [ts [Hts Hlen]].
    unfold outer_length_wf. subst. simpl.
    rewrite (@transpose_length bool). auto.
    intros t Ht. unfold oval_tapes_aux in Hts.
    destruct Hts as [Hlen' [Ht' Hspec]].
    specialize (Ht' t Ht). lia.
  }
  destruct (find_largest_true (cScanMatch (rPass (oreverse or)) (orev (w, vs)))) as [ lend' | ] eqn:E1.
  2 : discriminate.
  destruct (find_largest_true (cScanMatch or (oskipn (length w - lend') (w, vs)))) as [ d' | ] eqn:E2.
  2 : discriminate.
  rewrite reverse_pass_Some in E1; eauto.
  inversion H. subst n. subst d'. clear H.
  remember (length w - lend') as lend.
  rewrite forward_pass_Some in E2; eauto. 2 : lia.
  destruct E2 as [M M'].
  destruct E1 as [_ M''].
  split; [apply M | ].
  split.
  - apply M''.
  - apply M'.  
Qed.

Lemma llmatch_None : forall r w,
  llmatch r w = None
  -> forall n d, n <= n + d <= length w -> ~ match_regex r w n d.
Proof.
  intros.
  unfold llmatch in H.
  destruct (absEval (@cScanMatch A) w r) as [or vs] eqn:HabsEval.
  pose proof (absEval_spec (@cScanMatch A) w r cScanMatch_tape or vs HabsEval) as [Ho Hoval].
  assert (outer_length_wf (w, vs)) as Hwf. {
    unfold is_oval in Hoval. unfold is_oval_aux in Hoval.
    destruct Hoval as [ts [Hts Hlen]].
    unfold outer_length_wf. subst. simpl.
    rewrite (@transpose_length bool). auto.
    intros t Ht. unfold oval_tapes_aux in Hts.
    destruct Hts as [Hlen' [Ht' Hspec]].
    specialize (Ht' t Ht). lia.
  }
  destruct (find_largest_true (cScanMatch (rPass (oreverse or)) (orev (w, vs)))) as [ lend' | ] eqn:E1.
  2 : rewrite reverse_pass_None in E1; eauto.
  rewrite reverse_pass_Some in E1; eauto.
  destruct E1 as [E11 E12].
  destruct E11 as [d1 [Hd1 [Hd2 M]]].
  destruct (find_largest_true (cScanMatch or (oskipn (length w - lend') (w, vs)))) as [ d' | ] eqn:E2.
  1 : discriminate.
  rewrite forward_pass_None in E2; eauto. 2 : lia.
  specialize (E2 d1 ltac:(auto)). contradiction.
Qed.

Theorem llmatch_correct (r : @LRegex A) (w : list A) :
  (forall n d, llmatch r w = Some (n, d)
    -> match_regex r w n d (* match *)
    /\ (forall n', n' < n -> ~ (exists d', n' + d' <= length w /\ match_regex r w n' d')) (* leftmost *)
    /\ (forall d', d' > d -> n + d' <= length w -> ~ match_regex r w n d') (* longest *))
  /\
  (llmatch r w = None
    -> forall n d, n <= n + d <= length w -> ~ match_regex r w n d).
Proof.
  split.
  - apply llmatch_Some.
  - apply llmatch_None.
Qed.

End Layerwise.