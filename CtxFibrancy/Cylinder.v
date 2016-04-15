Require Import CtxFibrancy.Overture CtxFibrancy.Path_eq.
Set Universe Polymorphism.

Generalizable All Variables.

Module Export CylinderHIT.
  Private Inductive Cyl {X Y} (f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.

  Axiom fibrant_Cyl : forall {X Y} {f: X -> Y}, PFibrant (Cyl f).
  
  Axiom cyl_eq : forall {X Y} {f: X -> Y}, (base f) o f == top f.
  
  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.

  Definition Cyl_ind {X Y} {f: X -> Y}
             (P: forall y, Cyl f y -> Type) {FibP: PFibrant2 P}
             (top': forall x, P (f x) (top x))
             (base': forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.
End CylinderHIT.


Section Cylinder.
  Context {X Y} {f: X -> Y}.

  Definition Cyl_Contr (y: Y) : Contr (Cyl f y).
  Proof.
    exists (base y).
    revert y. use Cyl_ind.
    - exact cyl_eq.
    - intro. exact 1.
    - intros x; cbn.
      ref (transport_paths_r (x:= base (f x))_ (cyl_eq x) 1 @ _).
      exact (concat_1p _).
  Defined.

  (* ∃ y, Cyl f y  is the homotopy pushout of f and idmap *)
  Definition sig_cyl_ind (P: sigT (Cyl f) -> Type) {FibP: PFibrant P}
             (top': forall x, P (f x; top x))
             (base': forall y, P (y; base y))
             (cyl_eq': forall x,
                 transport (λ w, P (f x; w)) (cyl_eq x) (base' (f x)) = top' x)
    : forall w, P w.
  Proof.
    intros [y w].
    exact (Cyl_ind (λ y w, P (y; w)) top' base' cyl_eq' y w).
  Defined.

  Definition top' : X -> sigT (Cyl f) := λ x, (f x; top x).
  Definition base' : Y -> sigT (Cyl f) := λ y, (y; base y).
  Definition cyl_eq' `{Fibrant Y} : ∀ x, base' (f x) = top' x
    := λ x, path_sigma (Cyl f) 1 (cyl_eq x).
End Cylinder.