(** Operations on the [FSet A] for an arbitrary [A] *)
Require Import HoTT HitTactics.
Require Import finite_bags monad_interface.

Section operations.
  (** Monad operations. *)
  Definition bag_fmap {A B : Type} : (A -> B) -> bag A -> bag B.
  Proof.
    intro f.
    hrecursion.
    - exact ∅.
    - apply (fun a => {|f a|}).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
  Defined.

  Global Instance bag_pure : hasPure bag.
  Proof.
    intro.
    apply (fun a => {|a|}).
  Defined.  

  Global Instance fset_bind : hasBind bag.
  Proof.
    intros A.
    hrecursion.
    - exact ∅.
    - exact idmap.
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
  Defined.

  (** Bag-theoretical operations. *)
  Global Instance fset_comprehension : forall A, hasComprehension (bag A) A.
  Proof.
    intros A P.
    hrecursion.
    - apply ∅.
    - intro a.
      refine (if (P a) then {|a|} else ∅).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
  Defined.
        
  Definition single_product {A B : Type} (a : A) : bag B -> bag (A * B).
  Proof.
    hrecursion.
    - apply ∅.
    - intro b.
      apply {|(a, b)|}.
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
  Defined.

  Definition product {A B : Type} : bag A -> bag B -> bag (A * B).
  Proof.
    intros X Y.
    hrecursion X.
    - apply ∅.
    - intro a.
      apply (single_product a Y).
    - apply (∪).
    - apply assoc.
    - apply comm.
    - apply nl.
    - apply nr.
  Defined.

  Definition disjoint_sum {A B : Type} (X : bag A) (Y : bag B) : bag (A + B) :=
    (bag_fmap inl X) ∪ (bag_fmap inr Y).      

  Local Ltac remove_transport
    := intros ; apply path_forall ; intro Z ; rewrite transport_arrow
       ; rewrite transport_const ; simpl.
  Local Ltac pointwise
    := repeat (f_ap) ; try (apply path_forall ; intro Z2) ;
      rewrite transport_arrow, transport_const, transport_sigma
      ; f_ap ; hott_simpl ; simple refine (path_sigma _ _ _ _ _)
      ; try (apply transport_const) ; try (apply path_ishprop).

  Context `{Univalence}.

  (** [bag A] has decidable emptiness. *)  
  Definition isEmpty {A : Type} (X : bag A) : Decidable (X = ∅).
  Proof.
    hinduction X ; try (intros ; apply path_ishprop).
    - apply (inl idpath).
    - intros.
      refine (inr (fun p => _)).
      admit.
    - intros X Y H1 H2.
      destruct H1 as [p1 | p1], H2 as [p2 | p2].
      * left.
        rewrite p1, p2.
        apply nl.
      * right.
        rewrite p1, nl.
        apply p2.
      * right.
        rewrite p2, nr.
        apply p1.
      * right.
        intros p.
        apply p1.
        admit.
  Admitted.  
End operations.