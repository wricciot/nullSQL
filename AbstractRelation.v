Require Import Lists.List Lists.ListSet Vector Arith.PeanoNat.

(* sums a Vector of nats *)
Definition vec_sum {k} (nl : Vector.t nat k) :=
  Vector.fold_right plus nl 0.

Definition list_sum (nl : list nat) := List.fold_right plus 0 nl.

Module Type REL.
  Parameter R : nat -> Type.
  Parameter V : Type.
  Definition T := Vector.t V.
  Parameter memb   : forall n, R n -> T n -> nat.
  Parameter plus  : forall n, R n -> R n -> R n.
  Parameter minus : forall n, R n -> R n -> R n.
  Parameter inter : forall n, R n -> R n -> R n.
  Parameter times : forall m n, R m -> R n -> R (m + n).
  Parameter sum   : forall m n, R m -> (T m -> T n) -> R n.
  Parameter sel   : forall n, R n -> (T n -> bool) -> R n.
  Parameter flat  : forall n, R n -> R n.
  Parameter supp  : forall n, R n -> list (T n).

  Implicit Arguments memb [n].
  Implicit Arguments plus [n].
  Implicit Arguments minus [n].
  Implicit Arguments inter [n].
  Implicit Arguments times [m n].
  Implicit Arguments sum [m n].
  Implicit Arguments sel [n].
  Implicit Arguments flat [n].
  Implicit Arguments supp [n].

  Definition card := fun n S => memb (@sum n 0 S (fun _ => Vector.nil _)) (Vector.nil _).
  Implicit Arguments card [n].

  Parameter Rnil : R 0.
  Parameter Rone : R 0.
  (* generalized cartesian product of m relations, each taken with its arity n *)
  Fixpoint prod (Rl : list { n : nat & R n }) 
    : R (list_sum (List.map (projT1 (P := fun n => R n)) Rl)) :=
  match Rl as r return R (list_sum (List.map (projT1 (P := fun n => R n)) r)) with
  | List.nil => Rone
  | List.cons (existT _ x R) l0 => times R (prod l0)
  end.

  Hypothesis V_eqb : V -> V -> bool.
  Definition T_eqb {n} : T n -> T n -> bool := Vector.eqb _ V_eqb.

  Definition flatnat := fun n => match n with 0 => 0 | _ => 1 end.

  Hypothesis V_dec : forall (v w : V), {v = w} + {v <> w}.
  Hypothesis V_eqb_eq : forall (v w : V), V_eqb v w = true <-> v = w.
  Lemma T_dec : forall n, forall (x y : T n), {x = y} + {x <> y}.
  Proof.
    intros. eapply Vector.eq_dec. apply V_eqb_eq.
  Qed.
  Lemma T_eqb_eq : forall n, forall (v w : T n), T_eqb v w = true <-> v = w.
  Proof.
    intros. eapply Vector.eqb_eq. apply V_eqb_eq.
  Qed.

  Parameter p_fs : forall n, forall r : R n, forall t, memb r t > 0 -> List.In t (supp r).
  Parameter p_fs_r : forall n, forall r : R n, forall t, List.In t (supp r) -> memb r t > 0.
  Parameter p_nodup : forall n, forall r : R n, NoDup (supp r).
  Parameter p_plus : forall n, forall r1 r2 : R n, forall t, memb (plus r1 r2) t = memb r1 t + memb r2 t.
  Parameter p_minus : forall n, forall r1 r2 : R n, forall t, memb (minus r1 r2) t = memb r1 t - memb r2 t.
  Parameter p_inter : forall n, forall r1 r2 : R n, forall t, memb (inter r1 r2) t = min (memb r1 t) (memb r2 t).
  Parameter p_times : forall m n, forall r1 : R m, forall r2 : R n, forall t t1 t2, 
                      t = Vector.append t1 t2 -> memb (times r1 r2) t = memb r1 t1 * memb r2 t2.
  Parameter p_sum : forall m n, forall r : R m, forall f : T m -> T n, forall t, 
                    memb (sum r f) t = list_sum (List.map (memb r) (filter (fun x => T_eqb (f x) t) (supp r))).
  Parameter p_self : forall n, forall r : R n, forall p t, p t = false -> memb (sel r p) t = 0.
  Parameter p_selt : forall n, forall r : R n, forall p t, p t = true -> memb (sel r p) t = memb r t.
  Parameter p_flat : forall n, forall r : R n, forall t, memb (flat r) t = flatnat (memb r t).
  Parameter p_nil : forall r, memb Rnil r = 0.
  Parameter p_one : forall r, memb Rone r = 1.

  Parameter p_ext : forall n, forall r s : R n, (forall t, memb r t = memb s t) -> r = s.

End REL.