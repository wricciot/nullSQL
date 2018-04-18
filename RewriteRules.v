Require Import Eqdep Lists.List Lists.ListSet Vector Arith.PeanoNat Syntax AbstractRelation Bool.Sumbool Tribool 
  Semantics JMeq FunctionalExtensionality Omega Coq.Init.Specif.

Module RewriteRules (Db : DB) (Sql : SQL Db).
  Import Db.
  Import Sql.

  Module S2 := Sem2 Db.
  Module S3 := Sem3 Db.
  Module Ev := Evl Db Sql.
  Module SQLSem2 := SQLSemantics Db S2 Sql Ev.
  Module SQLSem3 := SQLSemantics Db S3 Sql Ev.

  Definition tml_of_scm s n := List.map (fun a => tmvar (n,a)) s.
  Definition btm_of_tml (tml : list pretm) (al : list Name) := List.combine tml al.
  Definition btm_of_scm s al n := btm_of_tml (tml_of_scm s n) al.

  Lemma commutative_join d G T1 T2 s1 s2 (j1 : j_tb d G T1 s1) (j2 : j_tb d G T2 s2) sa ja h :
    forall sb, sa = sb -> exists jb,
    forall ra rb, ra ~= rb ->
      Rel.memb (SQLSem3.q_sem d G (SELECT * FROM (T1::T2::Datatypes.nil) WHERE TRUE) sa ja h) ra =
      Rel.memb (SQLSem3.q_sem d G (SELECT (btm_of_tml (tml_of_scm s2 1 ++ tml_of_scm s1 2) sb) FROM (T2::T1::List.nil) WHERE TRUE) sb jb h) rb.
  Proof.
    dependent inversion ja with (fun G0 Q0 s0 Hinv => forall h0, h0 ~= h -> forall sb, s0 = sb ->
      exists jb : j_query d G (SELECT (btm_of_tml (tml_of_scm s2 1 ++ tml_of_scm s1 2) sb) FROM (T2::T1::List.nil) WHERE TRUE) sb,
      forall ra rb, ra ~= rb -> Rel.memb (SQLSem3.q_sem d G0 Q0 s0 Hinv h0) ra = 
        Rel.memb (SQLSem3.q_sem d G (SELECT (btm_of_tml (tml_of_scm s2 1 ++ tml_of_scm s1 2) sb) FROM (T2::T1::List.nil) WHERE TRUE) sb jb h) rb).
    intros h0 Hh0 sb Hsb. rewrite Hh0. clear h0 Hh0.
    cut (j_query d G
         (SELECT btm_of_tml (tml_of_scm s2 1 ++ tml_of_scm s1 2) sb FROM T2 :: T1 :: Datatypes.nil
          WHERE (TRUE)) sb).
    + rewrite e. intro Hcut. exists Hcut. intros ra.
      generalize Hsb; clear Hsb.
      dependent inversion Hcut with (fun G0 Q0 s0 Hinv => forall h0, h0 ~= h -> sa = s0 -> forall rb, ra ~= rb ->
        Rel.memb (SQLSem3.q_sem d G (SELECT * FROM T1 :: T2 :: Datatypes.nil WHERE (TRUE)) (concat g1)
     (j_selstar d G (T1 :: T2 :: Datatypes.nil) g1 (TRUE) (concat g1) false j j0 eq_refl j3) h) ra =
        Rel.memb (SQLSem3.q_sem d G0 Q0 s0 Hinv h0) rb).
      rewrite e0. intros h0 Hh0. rewrite Hh0. clear e e0 h0 Hh0.
      intros es rb er. simpl. repeat repeat rewrite eq_rect_r_eq_refl.
      do 2 rewrite Rel.p_sum.
      generalize 

End RewriteRules.