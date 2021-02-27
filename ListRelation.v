Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat AbstractRelation OrdType SortedList Omega JMeq Util.

Module MultiSet (O : OrdType.OrdType) <: REL.

  Module S := InsertionSort O.
  Import S.
  Module OV := OrdType.OrdVec O.

  Definition V := O.t.              (* values *)
  Definition T := Vector.t V.       (* tuples *)
  Definition R : nat -> Type := fun n => { l : list (T n) & is_sorted l = true }.

  Definition V_dec := O.eq_dec.
  Definition V_eqb := fun x y => if V_dec x y then true else false.
  Definition T_eqb {n} := fun x y => if OV.veq_dec n x y then true else false.

  (* internal list operations *)
  Definition list_minus {n} : list (T n) -> list (T n) -> list (T n)
    := fun l1 l2 => 
      let l := nodup (OV.veq_dec n) (l1 ++ l2) in
      List.fold_left (fun acc x => acc ++ 
        repeat x (count_occ (OV.veq_dec _) l1 x - count_occ (OV.veq_dec _) l2 x)) l List.nil.
  Definition list_inter {n} : list (T n) -> list (T n) -> list (T n)
    := fun l1 l2 => 
      let l := nodup (OV.veq_dec n) (l1 ++ l2) in
      List.fold_left (fun acc x => acc ++
        repeat x (min (count_occ (OV.veq_dec _) l1 x) (count_occ (OV.veq_dec _) l2 x))) l List.nil.
  Definition all_pairs {m} {n} : list (T m) -> list (T n) -> list (T m * T n)
    := fun l1 l2 => List.fold_left (fun acc x => acc ++ List.map (fun y => (x,y)) l2) l1 List.nil.
  Definition pair_dec {A} {B} : 
    (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
    (forall b1 b2 : B, {b1 = b2} + {b1 <> b2}) ->
    forall x y : A * B, {x = y} + {x <> y}.
  Proof.
    intros. decide equality.
  Qed.
  Definition list_times {m} {n} : list (T m) -> list (T n) -> list (T (m+n))
    := fun l1 l2 => 
      let l := nodup (pair_dec (OV.veq_dec m) (OV.veq_dec n)) (all_pairs l1 l2) in
      List.fold_left (fun acc x => acc ++
        repeat (Vector.append (fst x) (snd x)) 
          (count_occ (OV.veq_dec _) l1 (fst x) * count_occ (OV.veq_dec _) l2 (snd x))) l List.nil.
  Definition list_comp {m} {n} : list (T m) -> (T m -> T n) -> list (T n)
    := fun l0 f =>
      let l := nodup (OV.veq_dec _) l0 in
      List.fold_left (fun acc x => acc ++
        repeat (f x) (count_occ (OV.veq_dec _) l0 x)) l List.nil.
  Definition list_rcomp {m} {n} : list (T m) -> (T m -> list (T n)) -> list (T n)
    := fun l f =>
      let l1 := nodup (OV.veq_dec _) l in
      let l2 := nodup (OV.veq_dec _) (List.concat (List.map f l)) in
      List.fold_left 
        (fun acc t => acc ++ repeat t
          (list_sum (List.map (fun u => count_occ (OV.veq_dec _) l u * count_occ (OV.veq_dec _) (f u) t) l1)))
        l2 List.nil.

  (* public operations *)
  Definition memb {n} := fun (r : R n) t => count_occ (OV.veq_dec n) (projT1 r) t.
  Definition plus {n} : R n -> R n -> R n 
    := fun A B => existT _ (sort (projT1 A ++ projT1 B)) (sort_is_sorted _).
  Definition minus {n} : R n -> R n -> R n
    := fun A B => existT _ (sort (list_minus (projT1 A) (projT1 B))) (sort_is_sorted _).
  Definition inter {n} : R n -> R n -> R n
    := fun A B => existT _ (sort (list_inter (projT1 A) (projT1 B))) (sort_is_sorted _).
  Definition times {m} {n} : R m -> R n -> R (m + n)
    := fun A B => existT _ (sort (list_times (projT1 A) (projT1 B))) (sort_is_sorted _).
  Definition sum {m} {n} : R m -> (T m -> T n) -> R n
    := fun A f => existT _ (sort (list_comp (projT1 A) f)) (sort_is_sorted _).
  Definition rsum {m} {n} : R m -> (T m -> R n) -> R n
    := fun A f => existT _ (sort (list_rcomp (projT1 A) (fun x => projT1 (f x)))) (sort_is_sorted _).
  Definition sel {n} : R n -> (T n -> bool) -> R n
    := fun A p => existT _ (sort (List.filter p (projT1 A))) (sort_is_sorted _).
  Definition flat {n} : R n -> R n := fun A => existT _ (sort (nodup (OV.veq_dec n) (projT1 A))) (sort_is_sorted _).
  Definition supp {n} : R n -> list (T n) := fun A => nodup (OV.veq_dec n) (projT1 A).

  Implicit Arguments times [m n].
  Implicit Arguments sum [m n].
  Implicit Arguments sel [n].

  Definition card {n} := fun S => memb (@sum n 0 S (fun _ => Vector.nil _)) (Vector.nil _).

  Definition Rnil {n} : R n := existT _ (sort List.nil) (sort_is_sorted _).
  Definition Rone : R 0 := existT _ (sort (List.cons (Vector.nil _) List.nil)) (sort_is_sorted _).
  (* generalized cartesian product of m relations, each taken with its arity n *)
  Fixpoint prod (Rl : list { n : nat & R n }) 
    : R (list_sum (List.map (projT1 (P := fun n => R n)) Rl)) :=
  match Rl as r return R (list_sum (List.map (projT1 (P := fun n => R n)) r)) with
  | List.nil => Rone
  | List.cons (existT _ x R) l0 => times R (prod l0)
  end.

  Definition flatnat := fun n => match n with 0 => 0 | _ => 1 end.

  (* it was perhaps a bad idea to put these in the module type *)
  Lemma V_eqb_eq : forall (x y :V), V_eqb x y = true <-> x = y.
  Proof.
    intros. unfold V_eqb. destruct (V_dec x y); intuition. discriminate H.
  Qed.
  Lemma T_dec : forall n, forall (x y : T n), {x = y} + {x <> y}.
  Proof.
    intros. eapply Vector.eq_dec. apply V_eqb_eq.
  Qed.
  Lemma T_eqb_eq : forall n, forall (v w : T n), T_eqb v w = true <-> v = w.
  Proof.
    intros. unfold T_eqb. destruct (OV.veq_dec n v w); intuition. discriminate H.
  Qed.

  (* private proofs *)
  Lemma count_occ_repeat {A} {dec} (x:A) n : count_occ dec (repeat x n) x = n.
  Proof.
    induction n; simpl; intuition. destruct (dec x x); intuition.
  Qed.

  Lemma count_occ_repeat_neq {A} {dec} (x y : A) n : x <> y -> count_occ dec (repeat x n) y = 0.
  Proof.
    intro. induction n; simpl; intuition. destruct (dec x y); intuition.
  Qed.

  Lemma count_occ_app {A} {dec} l1 l2 (x:A) :
    count_occ dec (l1 ++ l2) x = count_occ dec l1 x + count_occ dec l2 x.
  Proof.
    induction l1; intuition.
    simpl. destruct (dec a x); intuition.
  Qed.

  Lemma count_occ_fold {A} {dec} l1 l2 f (l : list A):
    forall acc, NoDup l -> 
    (forall x, (0 < count_occ dec l1 x \/ 0 < count_occ dec l2 x) -> count_occ dec l x = 0 -> count_occ dec acc x = f x) ->
    (forall x, (0 < count_occ dec l1 x \/ 0 < count_occ dec l2 x) -> 0 < count_occ dec l x -> count_occ dec acc x = 0) ->
    forall x, (0 < count_occ dec l1 x \/ 0 < count_occ dec l2 x) ->
              count_occ dec (List.fold_left (fun acc' y => acc' ++ repeat y (f y)) l acc) x = f x.
  Proof.
    induction l; intuition.
    + simpl. apply IHl.
      - inversion H; assumption.
      - intros. destruct (dec a x0).
        rewrite e. rewrite count_occ_app. rewrite H1. simpl. rewrite count_occ_repeat. reflexivity.
        exact H2. rewrite e. simpl. destruct (dec x0 x0); intuition.
        rewrite count_occ_app. rewrite H0. rewrite count_occ_repeat_neq. omega. exact f0.
        exact H2. simpl. destruct (dec a x0); intuition.
      - intros. enough (a <> x0).
        rewrite count_occ_app. rewrite H1. rewrite count_occ_repeat_neq. reflexivity. exact H5.
        exact H2. simpl. destruct (dec a x0); intuition.
        inversion H. intro. apply H7. rewrite H9. eapply count_occ_In. exact H4.
      - left. exact H3.
    + simpl. apply IHl.
      - inversion H; assumption.
      - intros. destruct (dec a x0). 
        rewrite e. rewrite count_occ_app. rewrite H1. simpl. rewrite count_occ_repeat. reflexivity.
        exact H2. rewrite e. simpl. destruct (dec x0 x0); intuition.
        rewrite count_occ_app. rewrite H0. rewrite count_occ_repeat_neq. omega. exact f0.
        exact H2. simpl. destruct (dec a x0); intuition.
      - intros. enough (a <> x0).
        rewrite count_occ_app. rewrite H1. rewrite count_occ_repeat_neq. reflexivity. exact H5.
        exact H2. simpl. destruct (dec a x0); intuition.
        inversion H. intro. apply H7. rewrite H9. eapply count_occ_In. exact H4.
      - right. exact H3.
  Qed.

  Lemma count_occ_fold' {A} {dec} f (l : list A):
    forall acc,
    forall x, count_occ dec l x = 0 -> count_occ dec acc x = 0 ->
              count_occ dec (List.fold_left (fun acc' y => acc' ++ repeat y (f y)) l acc) x = 0.
  Proof.
    induction l; intuition. simpl.
    apply IHl. simpl in H. destruct (dec a x); intuition.
    rewrite count_occ_app. rewrite H0. rewrite count_occ_repeat_neq. reflexivity.
    simpl in H. destruct (dec a x); intuition.
  Qed.

  Lemma or_eq_lt_n_O n : n = 0 \/ 0 < n.
  Proof.
    destruct (Nat.eq_dec n 0); intuition.
  Qed.

  Lemma count_occ_nodup {A} {dec} l (x:A) : 
    count_occ dec (nodup dec l) x = 1 <-> 0 < count_occ dec l x.
  Proof.
    induction l; intuition.
    + simpl in H. discriminate H.
    + simpl in H1. destruct (in_dec dec a l); intuition.
      simpl. destruct (dec a x); intuition.
      simpl in H1. simpl. destruct (dec a x); intuition.
    + simpl. destruct (in_dec dec a l); intuition.
      apply H0. simpl in H1. destruct (dec a x); intuition.
      rewrite <- e. apply count_occ_In. exact i.
      simpl. simpl in H1. destruct (dec a x); intuition.
      f_equal. apply count_occ_not_In. intro. apply n.
      rewrite e. eapply nodup_In. exact H2.
  Qed.

  Lemma count_occ_nodup_O {A} {dec} l (x:A) : count_occ dec (nodup dec l) x = 0 <-> count_occ dec l x = 0.
  Proof.
    induction l; intuition.
    + simpl in H1. destruct (in_dec dec a l); intuition.
      enough (count_occ dec (nodup dec l) a = 1).
      simpl. destruct (dec a x); intuition. rewrite e in H0. rewrite H0 in H. discriminate H.
      apply NoDup_count_occ'. apply NoDup_nodup. apply nodup_In. exact i.
      simpl in H1. simpl. destruct (dec a x); intuition.
    + simpl. destruct (in_dec dec a l); intuition.
      simpl in H1. destruct (dec a x); intuition.
      simpl. simpl in H1. destruct (dec a x); intuition.
  Qed.

  (* internal properties of list_minus and list_inter *)
  Lemma count_occ_list_minus {n} l1 l2 :
    forall x, count_occ (OV.veq_dec n) (list_minus l1 l2) x
      = count_occ (OV.veq_dec n) l1 x - count_occ (OV.veq_dec n) l2 x.
  Proof.
    intro. unfold list_minus.
    destruct (or_eq_lt_n_O (count_occ (OV.veq_dec n) l1 x)).
    destruct (or_eq_lt_n_O (count_occ (OV.veq_dec n) l2 x)).
    rewrite H, H0. apply count_occ_fold'. apply count_occ_nodup_O.
    rewrite count_occ_app. rewrite H, H0. reflexivity.
    reflexivity.

    eapply (count_occ_fold l1 l2 (fun y => count_occ (OV.veq_dec n) l1 y - count_occ (OV.veq_dec n) l2 y)).
    apply NoDup_nodup. intros.
    pose (H3 := proj1 (count_occ_nodup_O _ _) H2); clearbody H3.
    rewrite count_occ_app in H3. destruct (count_occ (OV.veq_dec n) l1 x0); intuition.
    intros. reflexivity.
    right. exact H0.

    eapply (count_occ_fold l1 l2 (fun y => count_occ (OV.veq_dec n) l1 y - count_occ (OV.veq_dec n) l2 y)).
    apply NoDup_nodup. intros.
    pose (H2 := proj1 (count_occ_nodup_O _ _) H1); clearbody H2.
    rewrite count_occ_app in H2. destruct (count_occ (OV.veq_dec n) l1 x0); intuition.
    intros. reflexivity.
    left. exact H.
  Qed.

  Lemma count_occ_list_inter {n} l1 l2 :
    forall x, count_occ (OV.veq_dec n) (list_inter l1 l2) x
      = min (count_occ (OV.veq_dec n) l1 x) (count_occ (OV.veq_dec n) l2 x).
  Proof.
    intro. unfold list_inter.
    destruct (or_eq_lt_n_O (count_occ (OV.veq_dec n) l1 x)).
    destruct (or_eq_lt_n_O (count_occ (OV.veq_dec n) l2 x)).
    rewrite H, H0. apply count_occ_fold'. apply count_occ_nodup_O.
    rewrite count_occ_app. rewrite H, H0. reflexivity.
    reflexivity.

    eapply (count_occ_fold l1 l2 (fun y => min (count_occ (OV.veq_dec n) l1 y) (count_occ (OV.veq_dec n) l2 y))).
    apply NoDup_nodup. intros.
    pose (H3 := proj1 (count_occ_nodup_O _ _) H2); clearbody H3.
    rewrite count_occ_app in H3. destruct (count_occ (OV.veq_dec n) l1 x0); intuition.
    intros. reflexivity.
    right. exact H0.

    eapply (count_occ_fold l1 l2 (fun y => min (count_occ (OV.veq_dec n) l1 y) (count_occ (OV.veq_dec n) l2 y))).
    apply NoDup_nodup. intros.
    pose (H2 := proj1 (count_occ_nodup_O _ _) H1); clearbody H2.
    rewrite count_occ_app in H2. destruct (count_occ (OV.veq_dec n) l1 x0); intuition.
    intros. reflexivity.
    left. exact H.
  Qed.

  Fixpoint split {A} {m} {n} : Vector.t A (m+n) -> (Vector.t A m * Vector.t A n).
  refine
  (match m as m return Vector.t A (m+n) -> (Vector.t A m * Vector.t A n) with
   | 0 => fun v => (nil _,v)
   | S p => fun v => let h := Vector.hd v in let t := Vector.tl v in
      let (v1,v2) := split _ _ _ t in
      (Vector.cons _ h _ v1,v2)
   end).
  Defined.

  Lemma split_append {A} {m} {n} (l1 : Vector.t A m) (l2 : Vector.t A n) :
    split (append l1 l2) = (l1, l2).
  Proof.
    generalize l2. induction l1; simpl; intuition.
    rewrite IHl1. reflexivity.
  Qed.

  Lemma count_occ_hd {A} {dec} (a:A) l : 0 < count_occ dec (a::l) a.
  Proof.
    simpl. destruct (dec a a); intuition.
  Qed.

  Lemma count_occ_hd_neq {A} {dec} (a b:A) l : a <> b -> count_occ dec (a::l) b = count_occ dec l b.
  Proof.
    simpl. destruct (dec a b); intuition.
  Qed.

  Lemma count_occ_fold_times {m} {n} (l : list (T m*T n)) l1 l2 x1 x2:
    forall acc, NoDup l -> 
    (0 < count_occ (OV.veq_dec m) l1 x1 -> 0 < count_occ (OV.veq_dec n) l2 x2 -> 
      count_occ (pair_dec (OV.veq_dec _) (OV.veq_dec _)) l (x1,x2) = 0 ->
      count_occ (OV.veq_dec (m+n)) acc (append x1 x2) = count_occ (OV.veq_dec m) l1 x1 * count_occ (OV.veq_dec n) l2 x2) ->
    (0 < count_occ (OV.veq_dec m) l1 x1 -> 0 < count_occ (OV.veq_dec n) l2 x2 -> 
      0 < count_occ (pair_dec (OV.veq_dec _) (OV.veq_dec _)) l (x1,x2) ->
      count_occ (OV.veq_dec (m+n)) acc (append x1 x2) = 0) ->
    0 < count_occ (OV.veq_dec m) l1 x1 -> 0 < count_occ (OV.veq_dec n) l2 x2 ->
      count_occ (OV.veq_dec (m+n)) (List.fold_left 
        (fun acc' y => acc' ++ repeat (append (fst y) (snd y)) 
          (count_occ (OV.veq_dec m) l1 (fst y) * count_occ (OV.veq_dec n) l2 (snd y))) l acc)
        (append x1 x2) = count_occ (OV.veq_dec m) l1 x1 * count_occ (OV.veq_dec n) l2 x2.
  Proof.
    induction l; intuition.
    simpl. apply IHl.
    - inversion H; assumption.
    - intros. destruct (pair_dec (OV.veq_dec m) (OV.veq_dec n) (a0,b) (x1,x2)).
      injection e; intros. subst. rewrite count_occ_app. rewrite H4. simpl.
      rewrite count_occ_repeat. reflexivity.
      apply count_occ_hd.
      rewrite count_occ_app. rewrite H1. rewrite count_occ_repeat_neq. omega.
      intro; apply n0. rewrite <- (split_append x1 x2). rewrite <- H7. rewrite split_append. reflexivity.
      rewrite count_occ_hd_neq. exact H6. exact n0.
    - intros. enough ((a0,b) <> (x1,x2)).
      rewrite count_occ_app. rewrite H4. rewrite count_occ_repeat_neq. reflexivity.
      intro; apply H7. rewrite <- (split_append x1 x2). rewrite <- H8. rewrite split_append. reflexivity.
      rewrite count_occ_hd_neq. exact H6. exact H7.
      inversion H. intro. apply H9. injection H11; intros; subst. eapply count_occ_In. exact H6.
    - exact H2.
    - exact H3.
  Qed.

  Lemma count_occ_fold_times' {m} {n} {dec} f (l : list (T m*T n)):
    forall acc,
    forall x1 x2, f x1 x2 = 0 -> count_occ dec acc (append x1 x2) = 0 ->
      count_occ dec (List.fold_left (fun acc' y => acc' ++ repeat (append (fst y) (snd y)) (f (fst y) (snd y))) l acc) 
        (append x1 x2) = 0.
  Proof.
    induction l; intuition. simpl.
    apply IHl. exact H.
    rewrite count_occ_app. rewrite H0. simpl.
    destruct (pair_dec (OV.veq_dec m) (OV.veq_dec n) (x1,x2) (a0,b)).
    + injection e. intros. subst. rewrite H. reflexivity.
    + rewrite count_occ_repeat_neq. reflexivity.
      intro. apply n0.
      rewrite <- (split_append x1 x2). rewrite <- H1. rewrite split_append. reflexivity.
  Qed.

  Lemma In_all_pairs {m} {n} (x1 : T m) (x2 : T n) l1 l2 : 
    List.In x1 l1 -> List.In x2 l2 -> List.In (x1,x2) (all_pairs l1 l2).
  Proof.
    intros. unfold all_pairs.
    cut (forall acc l2, (List.In (x1,x2) acc \/ (List.In x1 l1 /\ List.In x2 l2)) -> 
      List.In (x1, x2) (List.fold_left (fun (acc : list (T m * T n)) (x : T m) => 
      acc ++ List.map (fun y : T n => (x, y)) l2) l1 acc)).
    intro. apply H1. right. split; assumption. clear H H0.
    induction l1; intuition.
    + contradiction (in_nil H).
    + simpl. apply IHl1. left. apply in_or_app. left. exact H0.
    + simpl. destruct H. 
      - subst. apply IHl1. left. apply in_or_app. right.
        induction l0. contradiction (in_nil H1).
        destruct H1. subst. left. reflexivity.
        right. apply IHl0. exact H.
      - apply IHl1. right. split; assumption.
  Qed.

  Lemma count_occ_list_times {m} {n} l1 l2 :
    forall x x1 x2, x = Vector.append x1 x2 -> count_occ (OV.veq_dec (m+n)) (list_times l1 l2) x
      = count_occ (OV.veq_dec m) l1 x1 * count_occ (OV.veq_dec n) l2 x2.
  Proof.
    intros. unfold list_times.
    destruct (or_eq_lt_n_O (count_occ (OV.veq_dec m) l1 x1)).
    + rewrite H0. simpl. rewrite H.
      apply (count_occ_fold_times'
        (fun x1 x2 => count_occ (OV.veq_dec m) l1 x1 * count_occ (OV.veq_dec n) l2 x2)).
      rewrite H0. reflexivity.
      reflexivity.
    + destruct (or_eq_lt_n_O (count_occ (OV.veq_dec n) l2 x2)).
      - rewrite H1. simpl. rewrite H. rewrite mult_0_r.
        apply (count_occ_fold_times'
          (fun x1 x2 => count_occ (OV.veq_dec m) l1 x1 * count_occ (OV.veq_dec n) l2 x2)).
        rewrite H1. apply mult_0_r.
        reflexivity.
      - rewrite H. apply count_occ_fold_times.
        * apply NoDup_nodup.
        * intros. enough (~List.In (x1, x2) (nodup (pair_dec (OV.veq_dec m) (OV.veq_dec n)) (all_pairs l1 l2))).
          contradiction H5. apply nodup_In. apply In_all_pairs.
          eapply count_occ_In. exact H0. eapply count_occ_In. exact H1.
          eapply count_occ_not_In. exact H4.
        * intros. reflexivity.
        * exact H0.
        * exact H1.
  Qed.

  Lemma filter_app : forall A (l l' : list A) p,
    List.filter p (l++l') = (List.filter p l)++(List.filter p l').
  Proof.
    intros A l. induction l; intuition; simpl.
    destruct (p a); simpl; auto. rewrite IHl. reflexivity.
  Qed.

(*
  Lemma list_sum_app : forall l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
  Proof.
    intros. induction l1; simpl; intuition.
 *)

  Lemma count_occ_list_comp {m} {n} l0 (f : T m -> T n) :
    forall t a l2, 
    (count_occ (OV.veq_dec n) a t =
     list_sum (List.map (count_occ (OV.veq_dec m) l0) (filter (fun x : T m => T_eqb (f x) t) l2))) ->
    count_occ (OV.veq_dec n)
      (List.fold_left (fun (acc : list (T n)) (x : T m) => acc ++ repeat (f x) (count_occ (OV.veq_dec m) l0 x))
        (nodup (OV.veq_dec m) l0) a) t =
    list_sum (List.map (count_occ (OV.veq_dec m) l0) (filter (fun x => T_eqb (f x) t) l2))
    + list_sum (List.map (count_occ (OV.veq_dec m) l0) (filter (fun x : T m => T_eqb (f x) t) (nodup (OV.veq_dec m) l0))).
  Proof.
    intro. induction (nodup (OV.veq_dec m) l0). simpl.
    + intros. rewrite H. omega.
    + intros. simpl. destruct (T_eqb (f a) t) eqn:Hfat.
      - simpl. rewrite plus_assoc. rewrite (IHl _ (a::l2)).
        * simpl. rewrite Hfat. simpl. omega.
        * rewrite count_occ_app. rewrite H. simpl. rewrite Hfat. simpl.
          rewrite plus_comm. f_equal.
          rewrite (proj1 (T_eqb_eq _ _ _) Hfat).
          rewrite count_occ_repeat. reflexivity.
      - rewrite (IHl _ l2). reflexivity.
        rewrite count_occ_app. rewrite H. rewrite count_occ_repeat_neq. omega.
        intro. rewrite H0 in Hfat. rewrite (proj2 (T_eqb_eq _ _ _) eq_refl) in Hfat. discriminate Hfat.
  Qed.

  Lemma list_sum_O l : (forall x, List.In x l -> x = 0) -> list_sum l = O.
  Proof.
    elim l; eauto. intros; simpl. rewrite (H0 a). apply H. 
    intros; apply H0. right; exact H1. left; reflexivity.
  Qed.

  Lemma list_sum_O' l : list_sum l = O -> forall x, List.In x l -> x = O.
  Proof.
    elim l.
    simpl; intros; contradiction H0.
    simpl; intros. destruct (plus_is_O _ _ H0). destruct H1; eauto.
    rewrite <- H1. exact H2.
  Qed.

  Lemma count_occ_list_rcomp {m} {n} l (f : T m -> list (T n)) :
    forall t,
    count_occ (OV.veq_dec n) (list_rcomp l f) t =
    list_sum (List.map 
      (fun u => count_occ (OV.veq_dec _) l u * count_occ (OV.veq_dec _) (f u) t) 
      (nodup (OV.veq_dec _) l)).
  Proof.
    intro. simpl. unfold list_rcomp.
    destruct (or_eq_lt_n_O (count_occ (OV.veq_dec n) (nodup (OV.veq_dec n) (concat (List.map f l))) t)).
    rewrite list_sum_O. rewrite count_occ_fold'; eauto.
    enough (count_occ (OV.veq_dec _) (List.concat (List.map f l)) t = O). clear H.
    intros.
    enough (List.In x (List.map (fun u => count_occ (OV.veq_dec _) l u * count_occ (OV.veq_dec _) (f u) t) l)).
    clear H. induction l in H0, H1 at 2 |- *.
    simpl in H1. contradiction.
    rewrite List.map_cons, concat_cons, count_occ_app in H0. destruct (plus_is_O _ _ H0); clear H0.
    rewrite List.map_cons in H1. destruct H1.
    rewrite <- H0, H. omega.
    apply IHl0. apply H2.
    apply H0.
    destruct (List.in_map_iff
     (fun u => count_occ (OV.veq_dec _) l u * count_occ (OV.veq_dec _) (f u) t)
     (nodup (OV.veq_dec _) l) x).
    destruct (H1 H); clear H1 H2. destruct H3.
    destruct (List.in_map_iff
     (fun u => count_occ (OV.veq_dec _) l u * count_occ (OV.veq_dec _) (f u) t)
     l x).
    apply H4. rewrite <- H1. exists x0. split; auto.
    destruct (nodup_In (OV.veq_dec _) l x0). auto.
    destruct (@count_occ_nodup_O _ (OV.veq_dec _) (concat (List.map f l)) t). auto.

    rewrite (count_occ_fold (nodup (OV.veq_dec n) (concat (List.map f l))) List.nil); eauto.
    apply NoDup_nodup.
    intros. destruct H0.
    rewrite H1 in H0. intuition.
    simpl in H0. intuition.
  Qed.

  (* public properties *)
  Lemma p_fs : forall n, forall r : R n, forall t, memb r t > 0 -> List.In t (supp r).
  Proof.
    intros n r t. destruct r. unfold memb, supp. simpl. intro.
    apply nodup_In. eapply count_occ_In. exact H.
  Qed.
  Lemma p_fs_r : forall n, forall r : R n, forall t, List.In t (supp r) -> memb r t > 0.
  Proof.
    intros n r t. destruct r. unfold memb, supp. simpl. intro.
    apply count_occ_In. eapply nodup_In. exact H.
  Qed.
  Lemma p_nodup : forall n, forall r : R n, NoDup (supp r).
  Proof.
    intros. destruct r. unfold supp. apply NoDup_nodup.
  Qed.

  Lemma p_plus : forall n, forall r1 r2 : R n, forall t, memb (plus r1 r2) t = memb r1 t + memb r2 t.
  Proof.
    intros. destruct r1. destruct r2. unfold memb. simpl.
    rewrite <- count_occ_sort. apply count_occ_app.
  Qed.
  Lemma p_minus : forall n, forall r1 r2 : R n, forall t, memb (minus r1 r2) t = memb r1 t - memb r2 t.
  Proof.
    intros. destruct r1. destruct r2. unfold memb; simpl.
    rewrite <- count_occ_sort. apply count_occ_list_minus.
  Qed.
  Lemma p_inter : forall n, forall r1 r2 : R n, forall t, memb (inter r1 r2) t = min (memb r1 t) (memb r2 t).
  Proof.
    intros. destruct r1. destruct r2. unfold memb; simpl.
    rewrite <- count_occ_sort. apply count_occ_list_inter.
  Qed.
  Lemma p_times : forall m n, forall r1 : R m, forall r2 : R n, forall t t1 t2, 
                    t = Vector.append t1 t2 -> memb (times r1 r2) t = memb r1 t1 * memb r2 t2.
  Proof.
    intros. destruct r1. destruct r2. unfold memb; simpl.
    rewrite <- count_occ_sort. apply count_occ_list_times. exact H.
  Qed.
  Lemma p_sum : forall m n, forall r : R m, forall f : T m -> T n, forall t, 
                    memb (sum r f) t = list_sum (List.map (memb r) (filter (fun x => T_eqb (f x) t) (supp r))).
  Proof.
    intros. destruct r. unfold memb, supp; simpl.
    rewrite <- count_occ_sort. clear e. unfold list_comp. 
    rewrite (count_occ_list_comp _ _ _ _ List.nil); reflexivity.
  Qed.

  Lemma p_self : forall n, forall r : R n, forall p t, p t = false -> memb (sel r p) t = 0.
  Proof.
    intros. destruct r. unfold memb; simpl.
    rewrite <- count_occ_sort. clear e. induction x; intuition.
    simpl. destruct (OV.veq_dec _ a t).
    + rewrite e. rewrite H. simpl. exact IHx.
    + destruct (p a). simpl. destruct (S.OV.veq_dec n a t); intuition. exact IHx.
  Qed.
  Lemma p_selt : forall n, forall r : R n, forall p t, p t = true -> memb (sel r p) t = memb r t.
  Proof.
    intros. destruct r. unfold memb; simpl.
    rewrite <- count_occ_sort. clear e. induction x; intuition.
    simpl. destruct (OV.veq_dec _ a t).
    + rewrite e. rewrite H. simpl. destruct (S.OV.veq_dec n t t); intuition.
    + destruct (p a). simpl. destruct (S.OV.veq_dec n a t); intuition. exact IHx.
  Qed.

  Lemma p_flat : forall n, forall r : R n, forall t, memb (flat r) t = flatnat (memb r t).
  Proof.
    intros. destruct r. unfold memb; simpl.
    rewrite <- count_occ_sort. clear e.
    destruct (in_dec (OV.veq_dec n) t x).
    + enough (exists m, count_occ (OV.veq_dec n) x t = S m). destruct H. rewrite H. simpl.
      apply NoDup_count_occ'. apply NoDup_nodup. apply nodup_In. exact i.
      enough (0 < count_occ (OV.veq_dec n) x t). inversion H; intuition; eauto.
      apply count_occ_In. exact i.
    + replace (count_occ (OV.veq_dec n) x t) with 0. simpl.
      apply count_occ_nodup_O. apply count_occ_not_In. exact n0.
      symmetry. apply count_occ_not_In. exact n0.
  Qed.
  Lemma p_nil : forall n (t : T n), memb Rnil t = 0.
  Proof.
    intros. reflexivity.
  Qed.
  Lemma p_one : forall r, memb Rone r = 1.
  Proof.
    intros. apply (case0 (fun x => memb Rone x = 1)).
    unfold memb, Rone. simpl. destruct (OV.veq_dec 0 (nil O.t) (nil O.t)); intuition.
  Qed.

  Lemma p_ext : forall n, forall r s : R n, (forall t, memb r t = memb s t) -> r = s.
  Proof.
    intros. destruct r. destruct s. unfold memb in H. simpl in H.

    assert (x = x0). 
    apply ext_eq. apply sorted_is_sorted; assumption. apply sorted_is_sorted; assumption. exact H.

    generalize e; clear e. rewrite H0. intros. f_equal.
    destruct e. apply JMeq_eq. destruct e0. reflexivity.
  Qed.

  Axiom rsum  : forall m n, R m -> (T m -> R n) -> R n.
  Implicit Arguments rsum [m n].

  Axiom Rsingle : forall n, T n -> R n.
  Implicit Arguments Rsingle [n].

  Axiom p_rsum : forall m n, forall r : R m, forall f : T m -> R n, forall t,
                    memb (rsum r f) t = list_sum (List.map (fun t0 => memb r t0 * memb (f t0) t) (supp r)).
  Axiom p_single : forall n (t : T n), memb (Rsingle t) t = 1.
  Axiom p_single_neq : forall n (t1 t2 : T n), t1 <> t2 -> memb (Rsingle t1) t2 = 0.

End MultiSet.