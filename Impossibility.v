Require Import Overture Strict_eq Category.

Hypothesis Fib : ∀ {x y : TYPE}, (x --> y) → Type.
Hypothesis ACofib : ∀ {x y : TYPE}, (x --> y) → Type.
Hypothesis wfs_AC_F : weak_factorization_system (@ACofib) (@Fib).

Let facto_AC_F := facto wfs_AC_F.

Let Id' (A: Type) : Type := (facto_AC_F A (A * A) (fun x => (x, x))).1.
Let r' {A: Type} : A -> Id' A := (facto_AC_F A (A * A) (fun x => (x, x))).2.1.
Let r'_AC {A} : ACofib (@r' A) := fst (snd (facto_AC_F A (A * A) (fun x => (x, x))).2.2.2).
Let π1' {A: Type} : Id' A -> A * A := (facto_AC_F A (A * A) (fun x => (x, x))).2.2.1.
Let π1'_F {A} : Fib (@π1' A) := snd (snd (facto_AC_F A (A * A) (fun x => (x, x))).2.2.2).
Let π1'_r' (A: Type) : (@π1' A) o r' ≡ fun x => (x, x)
  := fst ((facto_AC_F A (A * A) (fun x => (x, x))).2.2.2).
Let Id {A: Type} (x y: A) : Type := exists (w: Id' A), π1' w ≡ (x, y).
Let r {A: Type} (x: A) : Id x x :=
  (r' x; Eap10 (fst (facto_AC_F A (A * A) (fun x => (x, x))).2.2.2) x).

Let Fibrant (A: Type) : Type := Fib (fun _: A => tt).

Hypothesis fib_empty : Fibrant False.
Hypothesis fib_π1 : forall {A} (P: A -> Type) (H: forall x, Fibrant (P x)), Fib (π1 P).

Definition J {A: Type} (P: forall (x y: A) (p: Id x y), Type) (H: forall x y p, Fibrant (P x y p))
           (h: forall x, P x x (r x))
  : forall x y p, P x y p.
  transparent assert (r'' : (A -> exists (x y: A), Id x y)). {
    exact (fun x => (x; (x; r x))). }
  pose (P' := fun w : exists (x y: A), Id x y => P w.1 w.2.1 w.2.2).
  pose proof (LLP_R wfs_AC_F).
  specialize (X _ _ r''); cbn in X.
  ref (let X' := (fst X) _ in _). {
    apply X. intros Y Z g Hg F G e; cbn in *.
    pose proof (LLP_R wfs_AC_F). cbn in X0.
    specialize (X0 _ _ (@r' A)). apply fst in X0.
    specialize (X0 r'_AC Y Z g Hg F); cbn in *.
    ref (let X0' := X0 _ _ in _).
    unfold Id in G. intro w. exact (G (fst (π1' w); (snd (π1' w); (w; E1)))).
    refine (e E@ _).
    apply eq_funext; intro x; apply Eap; cbn. subst r''; cbn.
    pose proof (Eap10 (π1'_r' A) x); cbn in X1.
    set (fst (π1' (r' x))) in *.
    set (snd (π1' (r' x))) in *.
    pose proof (Eap fst X1 : y ≡ x).
    pose proof (Eap snd X1 : y0 ≡ x). clear X1.
    refine (eq_sigma _ X2^E _).
    rewrite Etransport_sigma'; cbn.
    refine (eq_sigma _ X3^E _).
    refine (Etransport_sigma' _ _ E@ _); cbn.
    ref (eq_sigma _ _ _). destruct X2^E. reflexivity.
    apply Eq_UIP. clearbody X0'.
    destruct X0' as [Ɣ [H1 H2]]. ref (_; _).
    exact (fun w => Ɣ w.2.2.1). split. exact H1.
    apply eq_funext; intros [x [y [w eq]]]; cbn.
    refine (Eap10 H2 w E@ _).
    set (fst (π1' w)) in *.
    set (snd (π1' w)) in *.
    pose proof (Eap fst eq : y0 ≡ x).
    pose proof (Eap snd eq : y1 ≡ y).
    apply Eap. refine (eq_sigma _ X1 _).
    rewrite Etransport_sigma'; cbn.
    refine (eq_sigma _ X2 _).
    refine (Etransport_sigma' _ _ E@ _); cbn.
    ref (eq_sigma _ _ _). destruct X1. reflexivity.
    apply Eq_UIP.
  } clearbody X'.
  specialize (X' _ _ (π1 P')).
  ref (let X'' := X' _ _ _ _ in _). apply fib_π1. intro; cbn. apply H.
  exact (fun x => ((x; (x; r x)); h x)).
  exact idmap. reflexivity.
  intros x y p. destruct X'' as [j [H1 H2]].
  pose (Eap10 H2 (x; (y; p))). cbn in e.
  set (j (x; (y; p))) in *. clearbody e. clearbody s.
  destruct s as [[x' [y' p']] u]; cbn in *.
  set e..2E. set  e..1E in *. cbn in *.
  clearbody e0. destruct e1. cbn in *.
  set e0..2E. set  e0..1E in *. cbn in *.
  clearbody e1. destruct e2. cbn in *. destruct e1.
  exact u.
Defined.


Let repl (A: Type) : Type := (facto_AC_F A unit (fun _ => tt)).1.
Let fib_repl (A: Type) : Fibrant (repl A).
  pose proof (snd (snd (facto_AC_F A unit (fun _ => tt)).2.2.2)).
  refine (_ E# X). apply eq_funext. intro; cbn.
  now destruct ((((facto_AC_F A unit (λ _ : A, tt)).2).2).1 x).
Defined.
Let η {A: Type} : A -> repl A := (facto_AC_F A unit (fun _ => tt)).2.1.
Let AC_η {A} : ACofib (@η A) := fst (snd (facto_AC_F A unit (fun _ => tt)).2.2.2).

Hypothesis I : Type.
Hypothesis zero : I.
Hypothesis one : I.
Hypothesis seg : Id zero one.
Hypothesis strict : zero ≡ one -> False.


Definition repl_rec {A B} {H: Fibrant B} (f: A -> B) : repl A -> B.
  pose proof (LLP_R wfs_AC_F).
  specialize (X A (repl A) η); cbn in X.
  ref (let X' := (fst X) _ in _). apply AC_η.
  specialize (X' B unit (fun _ => tt) H).
  specialize (X' f (fun _ => tt) E1); cbn in X'.
  exact X'.1.
Defined.


Definition lem : repl (zero ≡ one) -> False.
  refine (repl_rec strict). apply fib_empty.
Defined.

Definition lem2 : repl (zero ≡ one).
  pose proof (J (fun i i' _ => repl (i ≡ i')) (fun x y p => fib_repl _) (fun i => η (@refl I i))).
  specialize (X zero one seg); cbn in X.
  exact X.
Defined.

Definition inconsistency : False.
  exact (lem lem2).
Defined.

Print Assumptions inconsistency.


Definition ETP {A} {x y: A} (e: x ≡ y) : Id x y.
  destruct e. apply r.
Defined.

Definition i_eq {A} {x y : A} (e e': x ≡ y)
  : e ≡ e' -> Id (ETP e) (ETP e').
Proof. intro H. destruct H. apply r.
Defined.

Definition lem1 {A} (x y : A) (p : Id x y)
  : repl (forall (r : x ≡ y), Id p (ETP r)).
  revert x y p. apply J. intros; apply fib_repl.
  intro. apply η. intro e. apply (i_eq E1). apply Eq_UIP.
Defined.

Definition lem2' {A} (x:A) (p : Id x x)
  : (forall (r : x ≡ x) , Id p (ETP r)) ->  Id p (r x).
  intro f. specialize (f E1). exact f.
Defined.

Definition fib_Id {A} (x y: A) : Fibrant (Id x y).
  apply (RLP_L wfs_AC_F).
  pose proof (@π1'_F A). apply (RLP_L wfs_AC_F) in X.
  intros A' B' g Hg F G H; cbn in *.
  specialize (X _ _ g Hg (pr1 o F) (fun _ => (x, y))). cbn in X.
  specialize (X (eq_funext (fun x => (F x).2))).
  destruct X as [h [H1 H2]]. ref (_;_).
  intro y'. exists (h y'). exact (Eap10 H2 _). split.
  - apply eq_funext; intro x'. use eq_sigma. exact (Eap10 H1 _).
    apply Eq_UIP.
  - apply eq_funext. intro x'; destruct (G x'). reflexivity.
Defined.

Definition lem3 {A} (x: A) (p: Id x x) : Id p (r x).
  cut (repl (forall (r : x ≡ x), Id p (ETP r))).
  2: apply lem1. use repl_rec. apply fib_Id.
  apply lem2'.
Defined.

Print Assumptions lem3.

(* Definition concat {A} {x y z: A} (p: Id x y) (q: Id y z) : Id x z. *)
(*   revert x y p z q. use J. cbn. admit. *)
(*   cbn. auto. *)
(* Defined. *)

Definition inv {A} {x y: A} (p: Id x y) : Id y x.
  revert x y p. apply J. intros; apply fib_Id.
  apply r.
Defined.

(* Definition lem4 {A} (x: A) (p q: Id x x) : Id p q. *)
(*   eapply concat. apply lem3. *)
(*   apply inv. apply lem3. *)
(* Defined. *)

Definition fib_forall {A} {B: A -> Type} (H: forall x, Fibrant (B x))
  : Fibrant (forall x, B x).
  apply (RLP_L wfs_AC_F).
  intros A' B' g Hg F G e; cbn in *.
  ref (_;_). intros y x.
  specialize (H x); apply (RLP_L wfs_AC_F) in H.
  specialize (H _ _ g Hg (fun x' => F x' x) G e); cbn in *.
  destruct H as [h [H1 H2]]. exact (h y). split.
  - apply eq_funext; intro x'; cbn.
    apply eq_funext; intro x; cbn.
    set ((RLP_L wfs_AC_F (B x) unit (λ _ : B x, tt)).1 (H x) A' B' g Hg 
                                                    (λ x'0 : A', F x'0 x) G e).
    destruct s as [s1 [s2 s3]]; cbn in *.
    exact (Eap10 s2 _).
  - apply eq_funext; intro x; destruct (G x); reflexivity.
Defined.

Definition Id_UIP {A} (x y: A) (p q: Id x y) : Id p q.
  revert x y p q. use J; cbn.
  intros x y p. apply fib_forall, fib_Id.
  intros. apply inv. apply lem3.
Defined.

Print Assumptions Id_UIP.