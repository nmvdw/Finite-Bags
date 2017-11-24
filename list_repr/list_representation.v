(** Definition of Finite Sets as via lists. *)
Require Import HoTT HitTactics.
Require Export set_names.

Module Export FBagL.

  Section FBagL.
    Private Inductive FBagL (A : Type) : Type :=
    | Nil : FBagL A
    | Cns : A ->  FBagL A -> FBagL A.

    Arguments Cns {_} _ _.

    Global Instance fset_empty : forall A,hasEmpty (FBagL A) := Nil.

    Arguments Nil {_}.

    Global Instance fset_singleton : forall A, hasSingleton (FBagL A) A := (fun A x => Cns x Nil).

    Variable A : Type.
    Infix ";;" := Cns (at level 8, right associativity).

    Axiom comm_s : forall (a b : A) (x : FBagL A),
        a ;; b ;; x = b ;; a ;; x.

  Arguments Cns {_} _ _.
  Arguments comm_s {_} _ _.

  End FBagL.

  Infix ";;" := Cns (at level 8, right associativity).
  Arguments Cns {_} _ _.
  Arguments comm_s {_} _ _.