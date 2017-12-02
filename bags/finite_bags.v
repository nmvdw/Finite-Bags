(** Definitions of the Kuratowski-finite sets via a HIT.
    We do not need the computation rules in the development, so they are not present here.
*)
Require Import HoTT HitTactics.
Require Export set_names.

Module Export Bags.
  Section Bags.
    Private Inductive bag (A : Type) : Type :=
    | E : bag A
    | L : A -> bag A
    | U : bag A -> bag A -> bag A.

    Global Instance fset_empty : forall A, hasEmpty (bag A) := E.
    Global Instance fset_singleton : forall A, hasSingleton (bag A) A := L.
    Global Instance fset_union : forall A, hasUnion (bag A) := U.

    Variable (A : Type).

    Axiom assoc : forall (x y z : bag A),
        x ∪ (y ∪ z) = (x ∪ y) ∪ z.

    Axiom comm : forall (x y : bag A),
        x ∪ y = y ∪ x.

    Axiom nl : forall (x : bag A),
        ∅ ∪ x = x.

    Axiom nr : forall (x : bag A),
        x ∪ ∅ = x.

    Axiom trunc : IsHSet (bag A).

  End Bags.

  Arguments assoc {_} _ _ _.
  Arguments comm {_} _ _.
  Arguments nl {_} _.
  Arguments nr {_} _.

  Section bag_induction.
    Variable (A : Type)
             (P : bag A -> Type)
             (H :  forall X : bag A, IsHSet (P X))
             (eP : P ∅)
             (lP : forall a: A, P {|a|})
             (uP : forall (x y: bag A), P x -> P y -> P (x ∪ y))
             (assocP : forall (x y z : bag A)
                               (px: P x) (py: P y) (pz: P z),
                  assoc x y z #
                        (uP x (y ∪ z) px (uP y z py pz))
                  =
                  (uP (x ∪ y) z (uP x y px py) pz))
             (commP : forall (x y: bag A) (px: P x) (py: P y),
                  comm x y #
                       uP x y px py = uP y x py px)
             (nlP : forall (x : bag A) (px: P x),
                  nl x # uP ∅ x eP px = px)
             (nrP : forall (x : bag A) (px: P x),
                  nr x # uP x ∅ px eP = px).

    (* Induction principle *)
    Fixpoint bag_ind
             (x : bag A)
             {struct x}
      : P x
      := (match x return _ -> _ -> _ -> _ -> _ -> P x with
          | E => fun _ _ _ _ _ => eP
          | L a => fun _ _ _ _ _ => lP a
          | U y z => fun _ _ _ _ _ => uP y z (bag_ind y) (bag_ind z)
          end) H assocP commP nlP nrP.
  End bag_induction.

  Section bag_recursion.
    Variable (A : Type)
             (P : Type)
             (H: IsHSet P)
             (e : P)
             (l : A -> P)
             (u : P -> P -> P)
             (assocP : forall (x y z : P), u x (u y z) = u (u x y) z)
             (commP : forall (x y : P), u x y = u y x)
             (nlP : forall (x : P), u e x = x)
             (nrP : forall (x : P), u x e = x).

    (* Recursion princople *)
    Definition bag_rec : bag A -> P.
    Proof.
      simple refine (bag_ind A _ _ _ _ _ _ _ _ _)
      ; try (intros ; simple refine ((transport_const _ _) @ _)) ; cbn.
      - apply e.
      - apply l.
      - intros x y ; apply u.
      - apply assocP.
      - apply commP.
      - apply nlP.
      - apply nrP.
    Defined.
  End bag_recursion.

  Global Instance bag_recursion A : HitRecursion (bag A) :=
    {
      indTy := _; recTy := _;
      H_inductor := bag_ind A; H_recursor := bag_rec A
    }.
End Bags.


Section member.
  Context {A : Type} `{Univalence}.

  Ltac trunc_intros := repeat (let X := fresh in refine (Trunc_ind _ _) ; intros X).
  
  Definition member1 (a : A) : bag A -> Trunc 0 Type.
  Proof.
    hrecursion.
    - apply tr ; apply Empty.
    - intros b ; apply tr ; apply (merely (b = a)).
    - intros X Y.
      strip_truncations.
      apply (tr (X + Y)).
    - trunc_intros.
      cbn.
      apply (ap tr).
      refine (path_universe (equiv_sum_assoc _ _ _))^.
    - trunc_intros.
      cbn.
      apply (ap tr).
      refine (path_universe (equiv_sum_symm _ _)).
    - refine (Trunc_ind _ _).
      intros X' ; cbn.
      apply (ap tr).
      refine (path_universe (sum_empty_l _)).
    - refine (Trunc_ind _ _).
      intros X' ; cbn.
      apply (ap tr).
      refine (path_universe (sum_empty_r _)).
  Defined.

  Definition member2 (a : A) : bag A -> bag hProp.
  Proof.
    hrecursion.
    - apply ∅.
    - apply (fun b => {|merely  (b = a)|}).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
  Defined.
End member.
