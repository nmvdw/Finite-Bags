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
  induction p ; simpl.
  refine (ap (fun q => q @ _) (concat_p1 _) @ _).
  apply (concat_Vp _).
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
		 cnsP b (a ;; x) (cnsP a x px))
             (comm_reflP :
                forall (a b: A) (x: FBagL A) (px: P x),
                  let abxP := (cnsP a b ;; x (cnsP b x px)) in
                  let baxP := (cnsP b a ;; x (cnsP a x px)) in
                  let step1 := (transport_pp P (comm a b x) (comm b a x)) abxP in
                  let step2 :=
                      (ap (transport P (comm b a x)) (commP a b x px)) in
                  let step3 := commP b a x px in
                  step1 @ step2 @ step3 = transport2 P (comm_refl a b x) abxP).

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


    Axiom FSetC_ind_beta_comm_refl : forall (a b: A) (x : FBagL A),
        (apD02 FBagL_ind (comm_refl a b x)) =
        (coh a b x @ comm_reflP a b x (FBagL_ind x)) @ coh' a b x.


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
      simple refine (FBagL_ind A _ _ _ _ _);
        try (intros ; simple refine ((transport_const _ _) @ _)) ; cbn.
      - apply nilP.
      - apply (fun a _ px => cnsP a px).
      - apply commP.
      - intros. simpl.
        assert (Hapd1: transport2 (fun _ : FBagL A => P) (comm_refl a b x) (cnsP a (cnsP b px))
               = transport2 (fun _ : FBagL A => P) (comm_refl a b x) (cnsP a (cnsP b px))
                            @ apD (fun _ : FBagL A => (cnsP a (cnsP b px))) 1%path)
               by hott_simpl.
        rewrite Hapd1.
        refine (_ @ apD02 _ _ ).

         transitivity ((transport_pp
                         (fun _ : FBagL A => P) (comm a b x)
                         (comm b a x) (cnsP a (cnsP b px)))
                         @ ((ap (transport (fun _ : FBagL A => P) (comm b a x))
                         (apD (fun _ : FBagL A => cnsP a (cnsP b px)) (comm a b x)))
                              @ apD (fun _ : FBagL A => cnsP a (cnsP b px)) (comm b a x))).
         + rewrite !concat_pp_p.  f_ap.
           rewrite apD_const. rewrite ap_const.
           rewrite ap_pp.
           hott_simpl.  rewrite !concat_pp_p.  f_ap.
           rewrite apD_const. hott_simpl.
           assert ((transport (fun _ : FBagL A => P) (comm b a x)) == idmap).
           { intro z. apply transport_const. }
           rewrite (ap_f_eq_l _ _ (fun z => transport_const _ _ )).
           hott_simpl.
           rewrite concat_pp_p.
           rewrite comm_reflP. hott_simpl.
         + symmetry.
           refine (apD_pp (fun _ : FBagL A => cnsP a (cnsP b px)) (comm a b x) (comm b a x) @ _).
           hott_simpl.
    Defined.

  End FBagL_recursion.

End FBagL.

Section sum_lems.
  Context `{Univalence}.

  Lemma sum_assoc_map A B C : A + (B + C) -> (A + B) + C.
  Proof.
    intros [a | [b | c]] ; auto.
  Defined.

  Lemma sum_assoc_map_inv A B C : (A + B) + C -> A + (B + C).
  Proof.
    intros [[a | b] | c] ; auto.
  Defined.

  Global Instance sum_assoc_equiv A B C : IsEquiv (sum_assoc_map A B C).
  Proof.
    apply isequiv_biinv.
    split ; exists (sum_assoc_map_inv A B C).
    - intros [a | [b | c]] ; reflexivity.
    - intros [[a | b] | c] ; reflexivity.
  Defined.

  Lemma sum_assoc A B C : A + (B + C) <~> (A + B) + C.
  Proof.
    simple refine (BuildEquiv _ _ (sum_assoc_map A B C) _).
  Defined.

  Lemma sum_comm_map A B : A + B -> B + A.
  Proof.
    intros [a | b] ; auto.
  Defined.

  Global Instance sum_comm_equiv A B : IsEquiv (sum_comm_map A B).
  Proof.
    apply isequiv_biinv.
    split ; exists (sum_comm_map B A).
    - intros [a | b] ; reflexivity.
    - intros [a | b] ; reflexivity.
  Defined.

  Lemma sum_comm A B : A + B <~> B + A.
    simple refine (BuildEquiv _ _ (sum_comm_map A B) _).
  Defined.

  Lemma sum_comm_inv A B : sum_comm A B o sum_comm B A = 1%equiv.
  Proof.
    apply path_forall. intros [?|?]; reflexivity.
  Defined.
End sum_lems.

Section Membership.
  Context `{Univalence}.

Variable A : Type.

Definition member : A -> FBagL A -> Type.
  intros a.
  simple refine (FBagL_rec _ _ _ _ _ _ ).
  - apply Empty.
  - intros hd tl. apply (merely (hd = a) + tl).
  - intros x y tl. simpl.
    refine (path_universe (sum_assoc (Trunc -1 (x = a)) _ _) @ _).
    refine (ap (fun z => z + tl) (path_universe (sum_comm (Trunc -1 (x = a)) _  )) @ _).
    refine ((path_universe (sum_assoc (Trunc -1 (y = a)) _ _))^).
  - intros. simpl. hott_simpl.
    rewrite !concat_pp_p.
    rewrite (concat_p_pp (ap (fun z : Type => z + x) _) ).
    rewrite <- (ap_pp (fun z : Type => z + x)).
    rewrite <- (path_universe_compose (sum_comm _ _) (sum_comm  _ _)).
    (* TODO: Dan, look at this *)
    assert (path_universe (fun x0 : Trunc -1 (a0 = a) + Trunc -1 (b = a) =>
         (sum_comm (Trunc -1 (b = a)) (Trunc -1 (a0 = a)))
           ((sum_comm (Trunc -1 (a0 = a)) (Trunc -1 (b = a)))
              x0)) = idpath).
    { refine (_ @ path_universe_1).
      unfold path_universe. simpl.
      refine (ap path_universe_uncurried _).
      apply path_equiv.
      simpl.
      apply sum_comm_inv. }
    rewrite X. hott_simpl.
Defined.


End Membership.
