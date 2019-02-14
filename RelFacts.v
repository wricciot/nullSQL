Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat Bool.Sumbool JMeq 
  FunctionalExtensionality ProofIrrelevance Eqdep_dec EqdepFacts Omega Syntax AbstractRelation Util.

Module Facts (Db : DB) (Sql : SQL Db).

  Import Db.
  Import Sql.

(*** XXX: currently in Translation2V, needs to be shared (e.g. in Facts.v) ***)
  Lemma eq_memb_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n) r1 r2,
    S1 ~= S2 -> r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2.
  Proof.
    rewrite e. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma eq_times_dep m1 m2 n1 n2 (e1 : m1 = n1) (e2 : m2 = n2) :
    forall (R1 : Rel.R m1) (R2 : Rel.R m2) (S1 : Rel.R n1) (S2 : Rel.R n2),
    R1 ~= S1 -> R2 ~= S2 -> Rel.times R1 R2 ~= Rel.times S1 S2.
  Proof.
    rewrite e1, e2. intros. rewrite H, H0. reflexivity.
  Qed.

  Lemma p_ext_dep m n (e : m = n) : forall (S1 : Rel.R m) (S2 : Rel.R n),
      (forall r1 r2, r1 ~= r2 -> Rel.memb S1 r1 = Rel.memb S2 r2) -> S1 ~= S2.
  Proof.
    rewrite e. intros. apply eq_JMeq. apply Rel.p_ext. 
    intro. apply H. reflexivity.
  Qed.

  Lemma eq_T_eqb_iff {m} {n} (t1 t2 : Rel.T m) (t3 t4 : Rel.T n) : 
    (t1 = t2 <-> t3 = t4) -> Rel.T_eqb t1 t2 = Rel.T_eqb t3 t4.
  Proof.
    destruct (Rel.T_eqb t1 t2) eqn:e1; destruct (Rel.T_eqb t3 t4) eqn:e2; intuition; auto.
    + rewrite <- e2. symmetry. apply Rel.T_eqb_eq. apply H0. apply Rel.T_eqb_eq. exact e1.
    + rewrite <- e1. apply Rel.T_eqb_eq. apply H1. apply Rel.T_eqb_eq. exact e2.
  Qed.

  Lemma sum_ext m n R (f g : Rel.T m -> Rel.T n) : 
    (forall x, f x = g x) -> Rel.sum R f = Rel.sum R g.
  Proof.
    intro. apply Rel.p_ext. intro.
    do 2 rewrite Rel.p_sum. repeat f_equal. extensionality x.
    destruct (Rel.T_eqb (g x) t) eqn:e; rewrite <- H in e; exact e.
  Qed.

End Facts.
