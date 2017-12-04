(** Definition of Finite Bags using listish representation. *)
Require Import HoTT HitTactics.
Require Export set_names.

Lemma ap_f_eq_l
      {A B : Type}
      (f g : A -> B)
      (e : f == g)
      {a b : A}
      (p : a = b)
  : ap f p = e a @ ap g p @ (e b)^.
Proof.
  induction p ; simpl.
  refine (_ @ ap (fun q => q @ _) (concat_p1 _)^).
  apply (concat_pV _)^.
Defined.

Lemma ap_f_eq_r
      {A B : Type}
      (f g : A -> B)
      (e : f == g)
      {a b : A}
      (p : a = b)
  : (e a)^ @ ap f p @ e b = ap g p.
Proof.
  rewrite (ap_f_eq_l f g e). hott_simpl.
Defined.

Definition concat_Y
           {A : Type}
           {Y : A -> Type}
           {a b c : A}
           (p1 : a = b)
           (p2 : b = c)
           {x : Y a} {y : Y b} {z : Y c}
           (q1 : p1 # x = y)
           (q2 : p2 # y = z)
  : (p1 @ p2) # x = z.
Proof.
  refine (transport_pp Y p1 p2 x @ _).
  refine (ap (transport Y p2) q1 @ q2).
Defined.

Definition inverse_Y
           {A : Type}
           {Y : A -> Type}
           {a b : A}
           (p : a = b)
           {x : Y a} {y : Y b}
           (q : p # x = y)
  : p^ # y = x.
Proof.
  refine (ap (transport Y p^) q^ @ transport_Vp _ _ _).
Defined.

Lemma transport_const_pp
      {A B : Type}
      {a b c : A}
      (p1 : a = b)
      (p2 : b = c)
      (x : B)
  : transport_const (p1 @ p2) x
    =
    (transport_pp (fun _ : A => B) p1 p2 x)
      @ (transport_const p2 (transport (fun _ : A => B) p1 x))
      @ transport_const p1 x.
Proof.
  induction p1, p2.
  reflexivity.
Defined.

Lemma transport_const_V
      {A B : Type}
      {a b : A}
      (p : a = b)
      (x : B)
  : transport_const p^ x
    =
    (ap (transport _ p^) (transport_const p x)^)
      @ transport_Vp _ p x.
Proof.
  induction p ; reflexivity.
Defined.

Module Export FBagL.
  Section FBagL.
    Private Inductive FBagL (A : Type) : Type :=
    | Nil : FBagL A
    | Cns : A ->  FBagL A -> FBagL A.

    Global Instance fset_empty : forall A,hasEmpty (FBagL A) := Nil.

    Arguments Nil {_}.
    Arguments Cns {_} _ _.

    Global Instance fset_singleton :
      forall A, hasSingleton (FBagL A) A := (fun A x => Cns x Nil).

    Variable A : Type.

    Infix " ;;" := Cns (at level 8, right associativity).

    Axiom comm : forall (a b : A) (x : FBagL A),  a ;; b ;; x = b ;; a ;; x.

    Axiom comm_refl : forall (a b : A) (x : FBagL A),
        (comm a b x) @ (comm b a x) = idpath.
  End FBagL.

  Arguments Cns {_} _ _.
  Arguments comm {_} _ _.
  Arguments comm_refl {_} _ _.
  Infix " ;;" := Cns (at level 8, right associativity).

  Section FBagL_induction.
    Variable (A : Type)
             (P : FBagL A -> Type)
             (eP : P ∅)
             (cnsP : forall (a:A) (x: FBagL A), P x -> P (a ;; x))
             (commP : forall (a b: A) (x: FBagL A) (px: P x),
		 comm a b x # cnsP a (b ;; x) (cnsP b x px) =
		 cnsP b (a ;; x) (cnsP a x px)).
    Variable (comm_reflP :
                forall (a b : A) (x : FBagL A) (px : P x),
                  transport2 P (comm_refl a b x) (cnsP a b ;; x (cnsP b x px))
                  =
                  concat_Y (comm a b x)
                           (comm b a x)
                           (commP a b x px)
                           (commP b a x px)).

    (* Induction principle *)
    Fixpoint FBagL_ind
             (x : FBagL A)
             {struct x}
      : P x
      := (match x return _ -> _ -> P x with
          | Nil => fun _ _ => eP
          | a ;; y => fun _ _ => cnsP a y (FBagL_ind y)
          end) commP comm_reflP.

    Axiom FSetC_ind_beta_comm : forall (a b: A) (x : FBagL A),
        apD FBagL_ind (comm a b x) = commP a b x (FBagL_ind x).





    Lemma coh : forall (a b: A) (x: FBagL A),
        (apD FBagL_ind (comm a b x @ comm b a x)) =
        (let abxP := cnsP a b ;; x (cnsP b x (FBagL_ind x)) in
         let baxP := cnsP b a ;; x (cnsP a x (FBagL_ind x)) in
         let step1 := transport_pp P (comm a b x) (comm b a x) abxP in
         let step2 :=
             ap (transport P (comm b a x))
                (commP a b x (FBagL_ind x)) in
         let step3 := commP b a x (FBagL_ind x) in
         (step1 @ step2) @ step3).
    Proof.
      intros.
      simpl. rewrite <- FSetC_ind_beta_comm.
      simple refine ((apD_pp _ _ _) @ _).
      cbn. rewrite <- FSetC_ind_beta_comm.
      reflexivity.
    Defined.

    Lemma coh' : forall (a b: A) (x: FBagL A),
        transport2 P (comm_refl a b x)
                   (cnsP a b ;; x (cnsP b x (FBagL_ind x))) =
        transport2 P (comm_refl a b x)
                   (FBagL_ind a ;; b ;; x) @ apD FBagL_ind 1.
    Proof.
      intros.  hott_simpl.
    Defined.


(*    Axiom FSetC_ind_beta_comm_refl : forall (a b: A) (x : FBagL A),
        (apD02 FBagL_ind (comm_refl a b x)) =
        (coh a b x @ comm_reflP a b x (FBagL_ind x)) @ coh' a b x.
*)

  End FBagL_induction.

  Section FBagL_recursion.
    Variable (A : Type)
             (P : Type)
             (nilP : P)
             (cnsP : A -> P -> P)
             (commP : forall (a b: A) (x : P), cnsP a (cnsP b x) = cnsP b (cnsP a x))
             (comm_reflP:  forall (a b : A) (x: P), commP a b x @ commP b a x = idpath).

    (* Recursion princople *)
    Definition FBagL_rec : FBagL A -> P.
    Proof.
      simple refine (FBagL_ind A _ _ _ _ _).
      - apply nilP.
      - apply (fun a _ px => cnsP a px).
      - intros.
        refine ((transport_const _ _) @ commP _ _ _).
      - intros. simpl.
        apply (cancelR _ _ (transport_const 1 (cnsP a (cnsP b px)))).
        refine ((transport2_const (comm_refl a b x) (cnsP a (cnsP b px)))^ @ _).
        refine (transport_const_pp _ _ _ @ _).
        refine (_ @ (concat_p1 _)^).
        unfold concat_Y.
        refine (concat_pp_p _ _ _ @ ap _ _).
        rewrite (ap_f_eq_l _ _ (fun z => transport_const _ _ )).
        hott_simpl.
        rewrite !concat_pp_p.
        rewrite comm_reflP.
        refine (ap _ (concat_p1 _)^).
    Defined.
  End FBagL_recursion.

End FBagL.

Section Membership.
Context `{Univalence}.

(* TODO: Dan: PR this to the HoTT? *)
Lemma equiv_sum_symm_comm A B :
  (equiv_sum_symm A B = (equiv_sum_symm B A)^-1)%equiv.
Proof. by apply path_equiv. Defined.

Variable A : Type.

Definition member : A -> FBagL A -> Type.
  intros a.
  simple refine (FBagL_rec _ _ _ _ _ _ ).
  - apply Empty.
  - intros hd tl. apply (merely (hd = a) + tl).
  - intros x y tl. simpl.
    refine ((path_universe (equiv_sum_assoc (Trunc -1 (x = a)) _ _))^ @ _).
    refine (ap (fun z => z + tl) (path_universe (equiv_sum_symm _ _)) @ _).
    refine (path_universe (equiv_sum_assoc (Trunc -1 (y = a)) _ _)).
  - intros x y tl. hott_simpl.
    do 2 rewrite concat_pp_p.
    rewrite (concat_p_pp (ap (fun z : Type => z + tl) _) ).
    rewrite <- (ap_pp (fun z : Type => z + tl)).
    rewrite equiv_sum_symm_comm.
    rewrite path_universe_V.
    hott_simpl.
Defined.

End Membership.
