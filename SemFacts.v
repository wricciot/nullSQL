Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Bool.Sumbool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Syntax Semantics Util.

Module Facts (Db : DB) (Sql : SQL Db).

  Import Db.
  Import Sql.

  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module Ev := Evl Db Sql.
  Module SQLSem2 := SQLSemantics Db S2 Sql Ev.
  Module SQLSem3 := SQLSemantics Db S3 Sql Ev.

  Lemma projT1_env_app G1 G2 h1 h2 : 
    projT1 (Ev.env_app G1 G2 h1 h2) = projT1 h1 ++ projT1 h2.
  Proof.
    destruct h1. destruct h2. reflexivity.
  Qed.

  Lemma projT1_env_of_tuple G x : 
    projT1 (Ev.env_of_tuple G x) = to_list x.
  Proof.
    induction G.
    + simpl in x. eapply (case0 (fun v => List.nil = to_list v) _ x). Unshelve. reflexivity.
    + simpl. simpl in x. 
      enough (forall v1 v2, x = append v1 v2 -> 
        to_list v1 ++ projT1 (Ev.env_of_tuple G v2) = to_list x).
      erewrite <- (H (fst (split x)) (snd (split x))). reflexivity.
      apply JMeq_eq.
      apply (split_ind x (fun m n p => x ~= append (fst p) (snd p))).
      intros. rewrite H0. reflexivity.
      intros. rewrite H. rewrite to_list_append. f_equal. apply IHG.
  Qed.

  Lemma subenv1_app : forall G1 G2 h1 h2, Ev.subenv1 (Ev.env_app G1 G2 h1 h2) = h1.
  Proof.
    intros. destruct h1. destruct h2. unfold Ev.env_app. simpl.
    destruct (Nat.eqb_eq (length (concat (G1 ++ G2))) (length (x ++ x0))).
    unfold Ev.subenv1. apply Ev.env_eq. simpl. replace (length (concat G1)) with (length x).
    rewrite firstn_app. replace (length x - length x) with O.
    replace x with (x ++ firstn 0 x0) at 3. f_equal.
    apply List.firstn_all. rewrite firstn_O. apply app_nil_r.
    omega.
    symmetry. apply Nat.eqb_eq. exact e.
  Qed.

  Lemma env_app_nil_l : forall G h1 h2, Ev.env_app List.nil G h1 h2 = h2.
  Proof.
    intros. apply Ev.env_eq. destruct h1. simpl. replace x with (@List.nil Rel.V). reflexivity.
    destruct x; intuition.
    simpl in e. discriminate e.
  Qed.

  Lemma env_hd_hd : forall a s G (h : Ev.env ((a::s)::G)) x, 
    List.hd_error (projT1 h) = Some x -> Ev.env_hd h = x.
  Proof.
    intros. enough (hd_error (projT1 h) <> None).
    destruct h. unfold Ev.env_hd.
    rewrite (Ev.unopt_pi _ _ H0). generalize dependent H0. rewrite H. intro. reflexivity.
    rewrite H. intro. discriminate H0.
  Qed.

  Lemma env_tl_tl : forall a s G (h : Ev.env ((a::s)::G)),
    projT1 (Ev.env_tl h) = List.tl (projT1 h).
  Proof.
    intros. destruct h. simpl. reflexivity.
  Qed.

End Facts.