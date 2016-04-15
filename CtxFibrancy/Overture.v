(* -*- coq-prog-args: ("-top" "HTS.Overture" "-type-in-type") -*-  *)
Require Export ModelStructure.Overture.
Set Universe Polymorphism.


Axiom dummy_pfibrant_type : Type.
Class PFibrant {A: Type} (P: A -> Type) := { dummy_pfibrant_value : dummy_pfibrant_type }.

Axiom PFibrant_irrelevance : ∀ {A: Type} {P: A -> Type} (p q: PFibrant P),
    p ≡ q.

Notation "'Fibrant' A" := (PFibrant (λ _:unit, A)) (at level 30) : Fib_scope.
Notation "'PFibrant2' P" := (PFibrant (λ w, P w.1 w.2)) (at level 30) : Fib_scope.
Notation "'PFibrant3' P" := (PFibrant (λ w, P w.1 w.2.1 w.2.2)) (at level 30) : Fib_scope.
Open Scope Fib_scope.

Record FType := {
  FType_T : Type;
  FType_F : Fibrant FType_T
}.

Arguments Build_FType _ {_}.

Coercion FType_T : FType >-> Sortclass.
Global Existing Instance FType_F.


Axiom fibrant_Type : Fibrant Type.
(* Axiom fibrant_FType : Fibrant FType. *)

Axiom pfibrant_compose
  : forall A (B: A -> Type) {FibB: PFibrant B} A' (f: A' -> A), PFibrant (B o f).

Axiom pfibrant_forall : ∀ {A: Type} {B: A -> Type} {C: ∀ x, B x -> Type},
    PFibrant2 C -> PFibrant (λ x, ∀ y, C x y).

Axiom pfibrant_sigma : ∀ {A: Type} {B: A -> Type} {C: ∀ x, B x -> Type},
    PFibrant2 C -> PFibrant (λ x, ∃ y, C x y).

Instance fibrant_pfibrant A (B: A -> Type) {FibP: PFibrant B}
  : ∀ x, Fibrant (B x)
  := λ x, pfibrant_compose A B unit (λ _, x).
  
Instance fibrant_sigma A (B: A -> Type)
  : PFibrant B -> Fibrant (sigT B).
Proof.
  intros.
  ref (@pfibrant_sigma unit (λ _, A) (λ _ x, B x) _).
Defined.

Instance pfibrant_constant A B {FibB: Fibrant B}
  : PFibrant (λ _:A, B) | 50
  := pfibrant_compose unit (λ _, B) A (λ _, tt).



Instance pfibrant2_fibrant A (B: A -> Type) (C: forall x, B x -> Type) (H: PFibrant2 C)
  : forall x y, Fibrant (C x y).
intros x y; exact (@fibrant_pfibrant _ _ H (x; y)).
Defined.

Instance pfibrant2_pfibrant A (B: A -> Type) (C: forall x, B x -> Type) (H: PFibrant2 C)
  : forall x, PFibrant (C x) | 50.
intros x. exact (pfibrant_compose (sigT B) _ _ (λ y : B x, (x; y))).
Defined.

Instance pfibrant2_pfibrant_constant A B (C: A -> B -> Type) (H: PFibrant2 C)
  : forall x, PFibrant (C x).
intros x. exact (pfibrant_compose (sigT (λ _, B)) _ _ (λ y, (x; y))).
Defined.

Instance pfibrant2_pfibrant'_constant A B (C: A -> B -> Type) (H: PFibrant2 C)
  : forall y, PFibrant (λ x, C x y) | 50.
intros y. exact (pfibrant_compose _ _ _ (λ x, (x; y))).
Defined.



Module Export Paths.
  Private Inductive paths {A : Type} {FibA: Fibrant A} (a : A) : A -> Type :=
    idpath : paths a a.

  Arguments idpath {A FibA a} , [A FibA] a.

  Definition paths_ind (A : Type) {FibA: Fibrant A} (a : A)
             (P : forall a0 : A, paths a a0 -> Type) {FibP: PFibrant (λ w, P w.1 w.2)}
             (f: P a idpath) (y : A) (p : paths a y) : P y p
    := match p as p0 in (paths _ y0) return (P y0 p0) with
       | idpath => f
       end.
  Arguments paths_ind [A] [_] a P [_] f y p.
  
  Definition paths_rec (A : Type) {FibA: Fibrant A} (a : A) (P : A -> Type)
             {FibP: PFibrant P} (f : P a) (y : A) (p : paths a y)
    : P y := 
    match p in (paths _ y0) return (P y0) with
    | idpath => f
    end.

  Axiom pfibrant_paths : PFibrant (λ (X: ∃ (A: FType) (x: A), A), @paths X.1 _ X.2.1 X.2.2).

  Instance pfibrant_paths_constant (A: Type) {FibA: Fibrant A}
    : PFibrant2 (@paths A _).
  ref (@pfibrant_compose _ _ pfibrant_paths _ (λ w, (Build_FType A; w.1; w.2))).
  Defined.
  
  Definition inverse {A : Type} {FibA: Fibrant A} {x y : A} (p : paths x y) : paths y x
    := @paths_rec A _ x (fun y => paths y x) _ idpath y p.
  
  Definition paths_rec' A {FibA: Fibrant A} a y P {FibP: PFibrant P} (X : P y)
             (H : @paths A FibA a y) : P a
    := @paths_rec A FibA y P FibP X _ (inverse H).

  (* Declare ML Module "myrewrite". *)
End Paths.

Arguments paths_rec [A] [_] a P [_] f y p.

Notation "x = y :> A" := (@paths A _ x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Notation "f == g" := (forall x, f x = g x) (at level 70, no associativity) : type_scope.

Axiom path_funext: forall {A} {FibA: Fibrant A} {P: A -> Type} {FibP: PFibrant P}
                          {FibAP: Fibrant (∀ y : A, P y)} {f g : forall x : A, P x},
    f == g -> f = g.


Instance pfibrant_paths_FlFr A (P: A -> Type) {FibP: forall x, Fibrant (P x)} 
         (f g: ∀ x, P x)
  : PFibrant (λ x, f x = g x) | 100.
Proof.
  ref (@pfibrant_compose _ _ pfibrant_paths _ (λ x, (Build_FType (P x); f x; g x))).
Defined.

Tactic Notation "rew" open_constr(H)
  := rewrite H; auto with typeclass_instances.
Tactic Notation "rewi" open_constr(H)
  := rewrite <- H; auto with typeclass_instances.

(* Lemma paths_rew_test A {FibA: Fibrant A} a y P {FibP: PFibrant P} (X : P a) (H : a = y :> A) : P y. *)
(* Proof. rewi H. Defined. *)

Lemma paths_rew_r_test A {FibA: Fibrant A} a y P {FibP: PFibrant P} (X : P y) (H : a = y :> A) : P a.
Proof. rew H. Defined.

Definition Eq_to_paths {A : Type} {x y : A} {FibA: Fibrant A} (p : x ≡ y) : x = y :=
  match p with
    | refl => idpath
  end.


Definition concat {A : Type} {FibA: Fibrant A} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
  ref (@paths_rec A _ y (fun z => x = z) _
                  (@paths_rec A _ x (fun y => x = y)_ idpath y p) z q).
  all: ref (pfibrant2_pfibrant _ _ (@paths A _) _ _).
Defined.

Arguments concat {A FibA x y z} !p !q.

Delimit Scope path_scope with path.
Open Scope path_scope.

Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.
Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.
Notation "1" := idpath : path_scope.



Definition transport {A : Type} {FibA: Fibrant A} (P : A -> Type)
           {FibP: PFibrant P}  {x y : A} (p : x = y) (u : P x) : P y
  := paths_rec x P u y p.

Arguments transport {A}%type_scope {FibA} P {FibP} {x y} p%path_scope u : simpl nomatch.

Notation "p # x"
  := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.


Record Contr (A: Type) `{Fibrant A} :=
  { center : A;
    contr : ∀ x, center = x }.




Definition myid : forall A, A -> A := fun _ x => x.
Ltac mark H := let t := type of H in change (myid _ t) in H.
Ltac unmark H := let t := type of H in
                 match t with
                 | myid _ ?tt => change tt in H
                 end.

Ltac destruct_path p :=
  let t := type of p in
  match t with
    @paths _ _ ?x ?y =>
    mark p;
      repeat match goal with
             | [X: context[y] |- _] =>
               match type of X with
               | myid _ _ => fail 1
               | _ => revert X;
                   match goal with
                   | |- forall (X: ?T), ?G => change (forall (X: myid _ T), G)
                   end
               end
             end;
      unmark p;
      generalize y p; clear p y;
      match goal with
      | |- forall y p, @?P y p => let y := fresh y in
                                  let p := fresh p in
                                  intros y p; refine (paths_ind x P _ y p)
      end;
      repeat match goal with
             | |- forall (H: myid _ _), _ => let H := fresh H in
                                             intro H; unfold myid in H
             end
  end.
