Require Import CtxFibrancy.Overture CtxFibrancy.Path_eq.
Set Universe Polymorphism.

Module Export FibrantReplacement.

  Private Inductive repl (X: Type) : Type :=
  | η : X -> repl X.

  Arguments η {_} _.
  
  Axiom fibrant_repl : forall X, Fibrant (repl X).
  
  Definition repl_ind {X} (P: repl X -> Type) {FibP: PFibrant P}
             (H: forall x : X, P (η x))
    : forall z, P z.
  Proof.
    destruct z. apply H.
  Defined.
End FibrantReplacement.

Definition repl_rec {X P} {FibP: Fibrant P} (H: X -> P)
  : repl X -> P
  := repl_ind (λ _ : repl X, P) H.


Axiom pfibrant_repl_rec : ∀ A (P: A -> Type) {FibP: PFibrant P}, PFibrant (repl_rec P).
  
Definition repl_sigma {A} (B: repl A -> Type) {FibB: PFibrant B}
  : sigT B -> repl (sigT (B o η)).
Proof.
  intros [x y]; revert x y.
  use repl_ind; cbn. intros x y. exact (η (x; y)).
Defined.

Definition repl_J' {A} {x: A} (P: (∃ y: A, η x = η y) -> Type)
           {FibP: PFibrant P}
           {y: A} (p: η x = η y)
  : P (x; 1) -> P (y; p).
Proof.
  transparent assert (P' : ((∃ z, η x = z) → Type)). {
    refine (_ o repl_sigma (λ z, η x = z)).
    use repl_rec. exact P. }
  change (P' (η x; 1) -> P' (η y; p)).
  intro u; refine (paths_rec (η x; 1) P' u (η y; p) _).
  subst P'. classes.
  ref (path_sigma (λ z, η x = z) p _).
  exact (transport_paths_r _ p 1 @ concat_1p p).
Defined.
  
Definition repl_J {A} {x: A} (P: ∀ (y: A), η x = η y -> Type)
           {H: PFibrant (λ w: ∃ y, η x = η y, P w.1 w.2)}
           {y: A} (p: η x = η y)
  : P x 1 -> P y p.
Proof.
  ref (repl_J' (λ w, P w.1 w.2) p).
Defined.


Axiom repl_rec_eta : forall {X P} {FibP: Fibrant P} (f: repl X -> P),
    repl_rec (f o η) ≡≡ f.

Definition repl_eta {X P} {FibP: Fibrant P} (f g: repl X -> P)
  : f o η ≡≡ g o η -> f ≡≡ g.
Proof.
  intros H x.
  refine ((repl_rec_eta f x)^E E@ _ E@ repl_rec_eta g _).
  use Eap10.
  exact (Eap _ (eq_funext H)).
Defined.

Definition repl_f {A B} (f: A -> B) : repl A -> repl B.
Proof.
  apply repl_rec. exact (η o f).
Defined.

Definition repl_f_compose {A B C} (f: A -> B) (g: B -> C)
  : repl_f g o repl_f f ≡≡ repl_f (g o f).
Proof.
  use repl_eta; now intro.
Defined.

Definition repl_f_idmap A
  : repl_f (λ x: A, x) ≡≡ idmap.
Proof.
  use repl_eta; now intro.
Defined.
