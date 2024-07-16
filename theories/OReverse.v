(**

This file is the analogue of [Reverse.v] for the type [ORegex]. It contains the following:
  1. The definition of [oreverse] which reverses an [ORegex].
  2. The lemma [oreverse_match_iff] which describes the relationship between [r : ORegex] and [oreverse r : ORegex] with respect to [match_oregex].

*)

Require Import Lia.
Require Import Coq.Lists.List.

Require Import ORegex.

Section OReverse.

Context {A : Type}.

Fixpoint oreverse (r : @ORegex A) : ORegex  :=
  match r with
  | OEpsilon => OEpsilon
  | OCharClass c => OCharClass c
  | OUnion r1 r2 => OUnion (oreverse r1) (oreverse r2)
  | OConcat r1 r2 => OConcat (oreverse r2) (oreverse r1)
  | OStar r => OStar (oreverse r)
  | OQueryPos i => OQueryPos i
  | OQueryNeg i => OQueryNeg i
  end.

Lemma oreverse_involutive :
  forall r, 
    oreverse (oreverse r) = r.
Proof.
  induction r; simpl; congruence.
Qed.

Lemma oreverse_match :
  forall r ostr,
    outer_length_wf ostr
    -> match_oregex r ostr
    -> match_oregex (oreverse r) (orev ostr).
Proof.
  intros r ostr.
  destruct ostr as (w, o).
  unfold orev. simpl.
  revert w o. 
  induction r; simpl; intros w o Hwf; intros.
  - inversion H. apply omatch_epsilon.
    unfold olength in *. simpl in *.
    now rewrite rev_length.
  - inversion H. simpl in H2.
    apply omatch_charclass with (a := a).
    + unfold olength in *. simpl in *.
      rewrite rev_length. auto.
    + simpl. unfold olength in H1. 
      destruct w; 
        [simpl in H1; lia 
          | destruct w; 
          [ | simpl in H1; lia]].
      simpl in H2. inversion H2. subst.
      auto.
    + auto.  
  - inversion H. subst.
    remember (ofirstn n (w, o)) as ostr1.
    remember (oskipn n (w, o)) as ostr2.
    (destruct ostr1 as (w1, o1); destruct ostr2 as (w2, o2)).
    apply IHr1 in H2. apply IHr2 in H4.
    replace (rev w1, rev o1) with (orev (w1, o1)) in H2 by reflexivity.
    replace (rev w2, rev o2) with (orev (w2, o2)) in H4 by reflexivity.
    rewrite Heqostr1 in H2. rewrite Heqostr2 in H4.
    assert (n <= olength (w, o) \/ n > olength (w, o)) as Hlen by lia.
    destruct Hlen.
    + assert (n = (olength (w, o) - (olength (w, o) - n))) by lia.
    rewrite H1 in H2. rewrite H1 in H4.
    rewrite <- ofirstn_orev in H4 by assumption.
    rewrite <- oskipn_orev in H2 by assumption.
    unfold olength in H2. simpl in H2.
    unfold olength in H4. simpl in H4.
    unfold orev in H2. unfold orev in H4.
    simpl in H2. simpl in H4.
    apply omatch_concat with (n := length w - n); assumption.
    + unfold olength in H0. simpl in H0.
      assert ((w1, o1) = (w, o)).
      { rewrite ofirstn_all2 in Heqostr1.
        auto. assumption.
        unfold olength. simpl. lia.
      }
      rewrite H1 in Heqostr1.
      rewrite <- Heqostr1 in H2.
      apply omatch_concat with (n := 0); auto.
      rewrite oskipn_all3 in H4.
      replace (olength (w, o)) with (olength (w, o) - 0) in H4 by lia.
      rewrite <- ofirstn_orev in H4 by auto.
      auto. auto. unfold olength. simpl. lia.
    + rewrite Heqostr2. 
      apply oskipn_outer_length_wf. assumption. 
    + rewrite Heqostr1. 
      apply ofirstn_outer_length_wf. assumption.
  - inversion H; subst.
    + apply omatch_union_l.
      apply IHr1; assumption.
    + apply omatch_union_r.
      apply IHr2; assumption.
  - replace (OStar (oreverse r)) with (oreverse (OStar r)) by auto.
    remember (OStar r) as r'. remember (w, o) as ostr.
    replace (rev w, rev o) with (orev (w, o)) by auto.
    rewrite <- Heqostr. clear Heqostr. clear w o.
    revert Hwf. induction H; try discriminate.
    + inversion Heqr'. subst. intros.
      apply omatch_star_eps.
      unfold olength in *. simpl in *.
      rewrite rev_length. auto.
    + inversion Heqr'. subst. intros.
      simpl.
      assert (olength os = 0 \/ olength os > 0) as Hoslen by lia.
      destruct Hoslen; [
        apply omatch_star_eps; 
        destruct os as (w, o);
        unfold olength in *;
        simpl in *; 
        rewrite rev_length; auto | ].
      assert (n <= olength os \/ n > olength os) as Hn by lia.
      destruct Hn.
      * specialize (IHmatch_oregex2 ltac:(reflexivity)
          (oskipn_outer_length_wf n os Hwf)).
        simpl in IHmatch_oregex2.
        clear IHmatch_oregex1.
        apply omatch_star_r with (n := (olength os - n)).
        now apply orev_outer_length_wf.
        -- rewrite ofirstn_orev by assumption.
           replace (olength os - (olength os - n)) with n by lia.
           assumption.
        -- rewrite oskipn_orev by assumption.
           replace (olength os - (olength os - n)) with n by lia.
           destruct (ofirstn n os) as (w, o) eqn: He.
           unfold orev. simpl. apply IHr.
           rewrite <- He.
           apply ofirstn_outer_length_wf. assumption.
           assumption.
      * rewrite ofirstn_all2 in H.
        apply omatch_star with (n := olength os).
        ++ rewrite ofirstn_all2.
           destruct os as (w, o).
           unfold orev. simpl. apply IHr.
           auto. auto.
           now apply orev_outer_length_wf.
           pose proof (orev_olength os). lia.
        ++ apply omatch_star_eps.
           rewrite oskipn_all2. unfold olength. auto.
           now apply orev_outer_length_wf.
           pose proof (orev_olength os). lia.
        ++ assumption.
        ++ lia.  
  - inversion H. subst.
    unfold olength in H1. simpl in H1.
    apply omatch_query_pos with (v := v).
    + unfold olength. simpl. 
      now rewrite rev_length.
    + unfold outer_length_wf in Hwf.
      simpl in *.
      destruct o; 
        [ simpl in Hwf; lia |
          destruct o; 
            [| simpl in Hwf; lia]].
      auto.
    + auto.
  - inversion H. subst.
  unfold olength in H1. simpl in H1.
  apply omatch_query_neg with (v := v).
  + unfold olength. simpl. 
    now rewrite rev_length.
  + unfold outer_length_wf in Hwf.
    simpl in *.
    destruct o; 
      [ simpl in Hwf; lia |
        destruct o; 
          [| simpl in Hwf; lia]].
    auto.
  + auto.
Qed.

Lemma oreverse_match_iff :
  forall r ostr,
    outer_length_wf ostr
    -> match_oregex r ostr
    <-> match_oregex (oreverse r) (orev ostr).
Proof.
  intros. split.
  - intros. apply oreverse_match; assumption.
  - intros. rewrite <- oreverse_involutive with (r := r).
    rewrite <- orev_involutive with (s := ostr).
    apply oreverse_match. apply orev_outer_length_wf. assumption.
    assumption.
Qed.


End OReverse.