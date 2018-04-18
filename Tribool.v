Inductive tribool : Set := ttrue : tribool | tfalse : tribool | unknown : tribool.

Delimit Scope tribool_scope with tribool.

Bind Scope tribool_scope with tribool.

(** probably to be declared as a coercion *)
Definition tribool_of_bool (b : bool) : tribool := if b then ttrue else tfalse.

(** Basic boolean operators *)

Definition andtb (b1 b2:tribool) : tribool := 
  match b1, b2 with 
  | tfalse, _    => tfalse
  | _, tfalse    => tfalse
  | unknown, _  => unknown
  | _, unknown  => unknown
  | ttrue, ttrue  => ttrue
  end.

Definition ortb (b1 b2:tribool) : tribool := 
  match b1, b2 with
  | ttrue, _       => ttrue
  | _, ttrue       => ttrue
  | unknown, _    => unknown
  | _, unknown    => unknown
  | tfalse, tfalse  => tfalse
  end.

(*
Definition implb (b1 b2:bool) : bool := if b1 then b2 else true.

Definition xorb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => false
    | true, false => true
    | false, true => true
    | false, false => false
  end.
*)

Definition negtb (b:tribool) := match b with ttrue => tfalse | unknown => unknown | tfalse => ttrue end.

Infix "||" := ortb : tribool_scope.
Infix "&&" := andtb : tribool_scope.

Ltac destr_tribool :=
 intros; destruct_all tribool; simpl in *; trivial; try discriminate.

(** We have several interpretations of tribools as propositions *)

Definition Is_ttrue (b:tribool) :=
  match b with
    | ttrue => True
    | _ => False
  end.

Definition Is_tfalse (b:tribool) :=
  match b with
    | tfalse => True
    | _ => False
  end.

Definition Is_unknown (b:tribool) :=
  match b with
    | unknown => True
    | _ => False
  end.

(** Decidability *)
Lemma tribool_dec : forall b1 b2 : tribool, {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
Defined.

(*************)
(** * Equality *)
(*************)

Definition eqb (b1 b2:tribool) : bool :=
  match b1, b2 with
    | ttrue, ttrue => true
    | tfalse, tfalse => true
    | unknown, unknown => true
    | _, _ => false
  end.

Lemma eqb_subst :
  forall (P:tribool -> Prop) (b1 b2:tribool), eqb b1 b2 = true -> P b1 -> P b2.
Proof.
  destr_tribool.
Qed.

Lemma eqb_reflx : forall b:tribool, eqb b b = true.
Proof.
  destr_tribool.
Qed.

Lemma eqb_prop : forall a b:tribool, eqb a b = true -> a = b.
Proof.
  destr_tribool.
Qed.

Lemma eqb_true_iff : forall a b:tribool, eqb a b = true <-> a = b.
Proof.
  destr_tribool; intuition; discriminate.
Qed.

Lemma eqb_false_iff : forall a b:tribool, eqb a b = false <-> a <> b.
Proof.
  destr_tribool; intuition; discriminate.
Qed.

Lemma negtb_negtb (b : tribool) : negtb (negtb b) = b.
Proof.
  destr_tribool.
Qed.

Lemma negtb_andtb (b1 b2 : tribool) : negtb (andtb b1 b2) = ortb (negtb b1) (negtb b2).
Proof.
  destr_tribool.
Qed.

Lemma negtb_ortb (b1 b2 : tribool) : negtb (ortb b1 b2) = andtb (negtb b1) (negtb b2).
Proof.
  destr_tribool.
Qed.

Definition of_option_bool : option bool -> tribool :=
  fun x => match x with Some b => tribool_of_bool b | _ => unknown end.
