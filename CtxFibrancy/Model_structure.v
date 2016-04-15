Require Import CtxFibrancy.Overture Category CtxFibrancy.Fibrant_replacement Strict_eq CtxFibrancy.Path_eq CtxFibrancy.Equivalences CtxFibrancy.Cylinder.
Set Universe Polymorphism.


Set Implicit Arguments.
(* g is a retract of f *)
(* f in the middle, g on the side *)
Record Retract {A B} (g : A -> B) {A' B'} (f : A' -> B') :=
  { ret_s : A -> A' ;
    ret_r : A' -> A ;
    ret_s' : B -> B' ;
    ret_r' : B' -> B ;
    ret_sr : ret_r o ret_s ≡≡ idmap ;
    ret_sr' : ret_r' o ret_s' ≡≡ idmap;
    ret_H1 : f o ret_s ≡≡ ret_s' o g ;
    ret_H2 : ret_r' o f ≡≡ g o ret_r }.
Unset Implicit Arguments.

Global Arguments Build_Retract {A B g A' B' f} s r s' r' sr sr' H1 H2 : rename.

Infix "RetractOf" := Retract (at level 30).

Lemma LP_Retract {A A' B' B C C' D D'}
      {f: A -> A'} {g: B' -> B} {f': C -> C'} {g': D' -> D}
      (Hf : f' RetractOf f) (Hg : g' RetractOf g)
  : LP (C:=TYPE) f g -> LP (C:=TYPE) f' g'.
Proof.
  intros H F G H1; cbn in *.
  assert (X: g o (ret_s Hg o F o ret_r Hf) ≡≡ ret_s' Hg o G o ret_r' Hf o f). {
    intro. ref (ret_H1 Hg _ E@ _). apply Eap.
    ref (Eap10 H1 _ E@ _). apply Eap.
    exact (ret_H2 Hf _)^E. }
  specialize (H ((ret_s Hg) o F o (ret_r Hf)) ((ret_s' Hg) o G o (ret_r' Hf)) (eq_funext X)).
  destruct H as [h [H2 H3]]; cbn in *.
  exists ((ret_r Hg) o h o (ret_s' Hf)). split; apply eq_funext; intro x; simpl.
  - transitivity (ret_r Hg (h (f (ret_s Hf x)))).
    repeat apply Eap. exact (ret_H1 Hf _)^E.
    transitivity (ret_r Hg (ret_s Hg (F (ret_r Hf (ret_s Hf x))))).
    apply Eap. apply (Eap10 H2).
    transitivity (F (ret_r Hf (ret_s Hf x))).
    apply (ret_sr Hg). apply Eap. apply (ret_sr Hf).
  - ref ((ret_H2 Hg _)^E E@ _).
    ref (Eap _ (Eap10 H3 _) E@ _).
    ref (ret_sr' Hg _ E@ _).
    apply Eap. exact (ret_sr' Hf _).
Defined.

Definition retract_id {A B} (f: A -> B) : f RetractOf f.
Proof.
  use Build_Retract; intro; cbn; try reflexivity.
Defined.


Record IsFibration {A B} (f : A -> B) := (* F *)
  { fib_A : Type ;
    fib_P : fib_A -> Type ;
    fib_Fib : PFibrant fib_P;
    fib_H : f RetractOf (π1 fib_P) }.

Global Arguments Build_IsFibration {A B f B'} P {FibP} H : rename.

Notation Fib := @IsFibration.

Definition fiber {A B} (f: A -> B) := λ y, ∃ x, repl_f f x = η y.

Let f' {A B} (f: A → B) : A -> ∃ y, fiber f y
  := λ x, (f x ; η x ; 1).


Definition LP_f'_F {A B} (f: A → B)
  : LLP (C:=TYPE) Fib (f' f).
Proof.
  intros A'' B'' g [B' P HP Hg].
  refine (LP_Retract (retract_id _) Hg _).
  intros F G H; cbn in *.
  transparent assert (α: ((∃ y, fiber f y) -> ∃ y, P (G y))). {
    refine (λ y, (y; _)). destruct y as [y [x p]].
    revert x p. rapply @repl_ind. cbn; intros x p.
    pose proof (Etransport P (Eap10 H x) (F x).2); cbn in X.
    refine (repl_J (λ y p, P (G (y; (η x; p)))) p X). }
  transparent assert (β: ((∃ y, P (G y)) -> sigT P)). {
    exact (λ w, (G w.1; w.2)). }
  exists (β o α). split; [|reflexivity].
  apply eq_funext; intro x.
  use eq_sigma; cbn. exact (Eap10 H _)^E.
  now rewrite Etransport_Vp.
Defined.

Definition wfs_AC_F : weak_factorization_system (@LLP TYPE (@IsFibration)) (@IsFibration).
Proof.
  use Build_weak_factorization_system; cbn.
  - intros A B f. exists (∃ y, fiber f y).
    exists (f' f). exists (π1 _).
    split; [reflexivity|]. split.
    + apply LP_f'_F.
    + refine (Build_IsFibration _ (retract_id _)).
  - intros A B f; split; auto.
  - intros A B f; split; intros Hf.
    + intros A' B' g Hg. now apply Hg.
    + assert (LP (C:=TYPE) (f' f) f). {
        apply Hf. apply LP_f'_F. }
      specialize (X idmap (π1 _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine (Build_IsFibration (fiber f) _).
      refine (Build_Retract (f' f) g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _).
Defined.


Record AFib A B (f : A -> B) := (* F *)
  { afib_A : Type ;
    afib_P : afib_A -> Type ;
    afib_Fib : PFibrant afib_P ;
    afib_H1 : ∀ y, Contr (afib_P y) ;
    afib_H2 : f RetractOf (π1 afib_P) }.

Global Arguments Build_AFib {A B f B'} P {FibP} HP H : rename.

Definition AFib_Fib {A B} (f: A -> B)
  : AFib _ _ f -> Fib _ _ f.
Proof.
  intros [B' P FibP HP H].
  exact (Build_IsFibration _ H).
Defined.


Definition LP_top'_AF {A B} (f: A → B)
  : LLP (C:=TYPE) AFib (top' (f:=f)).
Proof.
  intros A'' B'' g [B' P FibP HP Hg].
  refine (LP_Retract (retract_id _) Hg _).
  clear g Hg. intros F G H; cbn in *.
  use exist.
  - intro w. exists (G w). revert w.
    use sig_cyl_ind; cbn.
    + intro x. exact ((Eap10 H x) E# (F x).2).
    + intro y. use center. apply HP.
    + intro; cbn. use path_contr.
      refine (_ E# (HP (G (f x; top x)))).
      apply PFibrant_irrelevance.
  - split; cbn. 2: reflexivity.
    apply eq_funext; intro x. use eq_sigma. exact (Eap10 H x)^E.
    rew Etransport_Vp. reflexivity.
Defined.

Definition wfs_C_AF : weak_factorization_system (@LLP TYPE AFib) AFib.
Proof.
  use Build_weak_factorization_system; cbn.
  - intros A B f. exists (sigT (Cyl f)).
    exists top'. exists (π1 _).
    split; [reflexivity|]. split.
    + apply LP_top'_AF.
    + ref (Build_AFib _ _ (retract_id _)); cbn.
      apply Cyl_Contr.
  - intros; split; auto.
  - intros A B f; split; intros Hf.
    + intros A' B' g Hg. now apply Hg.
    + assert (LP (C:=TYPE) (top' (f:=f)) f). {
        apply Hf. apply LP_top'_AF. }
      specialize (X idmap (π1 _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      ref (Build_AFib (Cyl f) _ _); cbn.
      apply Cyl_Contr.
      refine (Build_Retract top' g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _). 
Defined.


Definition weak_eq_retract {A B A' B'}
           (f: A -> B) (f': A' -> B')
           (Hf': f' RetractOf f) (Hf: IsEquiv (repl_f f))
  : IsEquiv (repl_f f').
Proof.
  destruct Hf as [g Hg1 Hg2].
  destruct Hf' as [s r s' r' sr sr' Hf1 Hf2].
  refine (isequiv_adjointify (repl_f r o g o repl_f s') _ _); intro.
  - rew repl_f_compose. rew (eq_funext Hf2)^E.
    rewi repl_f_compose. ref (ap _ (Hg1 _) @ _).
    rew repl_f_compose. rew (eq_funext sr'). apply Eq_to_paths, repl_f_idmap.
  - rew repl_f_compose. rewi (eq_funext Hf1). rewi (repl_f_compose s).
    ref (ap _ (Hg2 _) @ _). rew repl_f_compose.
    rew (eq_funext sr). rew repl_f_idmap. exact 1.
Defined.

Definition two_out_of_three_weak_equiv
  : @two_out_of_three TYPE (λ A B f, IsEquiv (repl_f f)).
Proof.
  intros A B C f g; cbn in *. repeat split; intros H1 H2.
  - rewrite <- (eq_funext (repl_f_compose f g)).
    now apply isequiv_compose.
  - rewrite <- (eq_funext (repl_f_compose f g)) in H2.
    apply (cancelL_isequiv (Hg:=H1) (Hgf:=H2) (repl_f g)).
  - rewrite <- (eq_funext (repl_f_compose f g)) in H1.
    apply (cancelR_isequiv (Hf:=H2) (Hgf:=H1) (repl_f f)).
Defined.


Definition AFib_aux {B} {P: B -> Type} {FibP: PFibrant P} (H: IsEquiv (repl_f (π1 P)))
  : ∀ y, Contr (P y).
Proof.
  destruct H as [g Hg1 Hg2 Hg3]. intro y.
  ref (let f := repl_ind (X:=sigT P) (λ z, repl_rec P (repl_f pr1 z)) pr2 in _).
  use Build_Contr.
  - change (repl_rec P (η y)).
    refine (transport (repl_rec P) (Hg1 (η y)) (f (g (η y)))).
  - intro w.
    specialize (Hg3 (η (y; w))); cbn in Hg3. rew Hg3.
    rew (transport_compose (repl_rec P) (repl_f (π1 (λ x : B, P x))) (Hg2 (η (y; w))) _)^.
    exact (irr_paths (apD f (Hg2 (η (y; w))))).
Defined.

Definition AFib_ok {A B} (f: A -> B)
  : AFib _ _ f  <->  (IsEquiv (repl_f f) × Fib _ _ f).
Proof.
  split; intro H.
  - split.
    + destruct H as [B' P FibP HP Hf].
      eapply weak_eq_retract. exact Hf. clear f Hf.
      use isequiv_adjointify.
      * use repl_rec. intro x. apply η. exists x. apply HP.
      * use repl_ind; cbn. intro; exact 1.
      * use repl_ind; cbn. intros [x w]; cbn.
        rew (contr _ _ w). exact 1.
    + destruct H as [B' P FibP H1 H2]. econstructor. eassumption. exact H2.
  - ref (Build_AFib (fiber f) _ _).
    + pose proof (two_out_of_three_weak_equiv _ _ _ (f' f) pr1); cbn in X.
      destruct X as [_ [_ H2]]. specialize (H2 (fst H)).
      refine (AFib_aux (P:=fiber f) (H2 _)).
      clear H2 H.
      use isequiv_adjointify.
      * use repl_rec. exact (λ w, w.2.1).
      * use repl_ind; cbn. intros [y [x p]]; cbn.
        revert x p. use repl_ind; cbn. intros x p; cbn.
        unfold f'. exact (repl_J (λ y p, η (f x; (η x; 1)) = η (y; (η x; p))) _ 1).
      * use repl_ind; cbn. intro; exact 1.
    + assert (LP (C:=TYPE) (f' f) f). {
        apply LP_f'_F. apply H. }
      specialize (X idmap pr1 E1); cbn in X. destruct X as [g [Hg1 Hg2]].
      refine (Build_Retract (f' f) g idmap idmap _ _ _ _);
        intro; try reflexivity; cbn.
      exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _).
Defined.

Definition LLPAFib_ok {A B} (f: A -> B)
  : LLP (C:=TYPE) Fib f  <->  (IsEquiv (repl_f f) × LLP (C:=TYPE) AFib f).
Proof.
  split.
  - intro H; split.
    + ref (let X := H _ B pr1 _ (f' f) idmap E1 in _).
      ref (Build_IsFibration _ (retract_id _)).
      destruct X as [g [Hg1 Hg2]]; cbn in *.
      use isequiv_adjointify.
      * use repl_rec. exact (λ w, (g w).2.1).
      * use repl_ind; cbn. intro x; pose (g x).2.2. cbn in *.
        rew p. apply Eq_to_paths, Eap. exact (Eap10 Hg2 _).
      * use repl_ind; cbn. intro x. rew (Eap10 Hg1 x).
        exact 1.
    + intros A' B' F Hf. apply H. now apply AFib_Fib.
  - intros [H2 H1] A' B' g Hg.
    ref (LP_Retract (f:=f' f) _ (retract_id _) _).
    +  clear A' B' g Hg.
       assert (X : AFib (∃ (y : B) (x : repl A), repl_f f x = η y) B pr1). {
         destruct H2 as [g Hg1 Hg2 Hg3].
         ref (Build_AFib _ _ (retract_id _)).
         intro y; cbn. exists (g (η y); Hg1 _).
         intros [x p].
         ref (path_sigma _ ((ap g p)^ @ Hg2 _) _).
         rew transport_paths_Fl. rew ap_pp. rew (Hg3 _)^.
         rew ap_V. rew inv_pp. rew inv_V.
         rew (ap_compose g (repl_f f) _)^.
         ref ( let X := _ : (λ x0 : repl B, repl_f f (g x0)) = idmap in _).
         ref (path_funext _); intro; cbn.
         exact (irr_paths (Hg1 _)).
         rew concat_pp_p.
         ref (irr_paths (moveR_Vp _ _ _ _)).
         set (η y) in *. clearbody r. clear y. destruct_path p.
         cbn. exact (concat_1p _ @ (concat_p1 _)^). }
       specialize (H1 (sigT (fiber f)) B pr1 X (f' f) idmap E1); clear X.
       destruct H1 as [Ɣ [H H']]; cbn in *.
       use (Build_Retract idmap idmap Ɣ pr1); intro; try reflexivity.
       exact (Eap10 H' _). exact (Eap10 H^E _).
    + now apply LP_f'_F.
Defined.


Definition fibrant_types_give_fibrations {A: Type} {FibA: Fibrant A}
  : IsFibration (λ _:A, tt).
Proof.
  ref (Build_IsFibration (λ _:unit, A) _).
  ref (Build_Retract (λ x, (tt; x)) (π2 (λ _:unit, A)) idmap idmap _ _ _ _);
    intro; try reflexivity; cbn.
  destruct x as [[] y]; reflexivity.
Defined.



Definition type_model_structure : model_structure TYPE.
Proof.
  rapply Build_model_structure.
  - exact (λ A B f, IsEquiv (repl_f f)).
  - exact Fib. 
  - exact (@LLP TYPE AFib).
  - apply two_out_of_three_weak_equiv.
  - eapply wfs_iff_R. apply @AFib_ok.
  (* exact wfs_C_AF. *)
    use Build_weak_factorization_system; cbn.
    + intros A B f. exists (sigT (Cyl f)).
      exists top'. exists (π1 _).
      split; [reflexivity|]. split.
      * apply LP_top'_AF.
      * ref (Build_AFib _ _ (retract_id _)); cbn.
        apply Cyl_Contr.
    + intros; split; auto.
    + intros A B f; split; intros Hf.
      * intros A' B' g Hg. now apply Hg.
      * assert (LP (C:=TYPE) (top' (f:=f)) f). {
          apply Hf. apply LP_top'_AF. }
        specialize (X idmap (π1 _) E1); cbn in X. destruct X as [g [Hg1 Hg2]].
        ref (Build_AFib (Cyl f) _ _); cbn.
        apply Cyl_Contr.
        refine (Build_Retract top' g idmap idmap _ _ _ _);
          intro; try reflexivity; cbn.
        exact (Eap10 Hg1 _). exact (Eap10 Hg2^E _). 
  - eapply wfs_iff_L. apply @LLPAFib_ok. exact wfs_AC_F.
Defined.

(* Print Assumptions type_model_structure. *)


(* F are retracts of their π1 : Σ fiber -> B *)
Definition F_caract {A B} {f: A -> B}
  : IsFibration f <-> ∃ (g: sigT (fiber f) -> A), f o g ≡≡ pr1 × g o (f' f) ≡≡ idmap.
Proof.
  split.
  - intros [B' P FibP [s r s' r' rs rs' H1 H2]].
    use exist.
    + intros [y [x p]]. apply r. exists (s' y).
      revert x p. use repl_ind; cbn. intros x p.
      ref (repl_J (λ y _, P (s' y)) p _); cbn.
      ref ((H1 x) E# _). exact (s x).2.
    + split; cbn.
      * intros [y [x p]]; cbn.
        ref ((H2 _)^E E@ _); cbn. apply rs'.
      * intro x. ref (_ E@ rs x).
        apply Eap. use eq_sigma. exact (H1 _)^E.
        apply Etransport_Vp.
  - intros [g [H1 H2]].
    ref (Build_IsFibration (fiber f) _).
    ref (Build_Retract (f' f) g idmap idmap _ _ _ _);
      intro; cbn; try reflexivity.
    apply H2. sym H1.
Defined.


(* AC are retracts of their f' *)
Definition AC_caract {A B} (f: A -> B)
  : LLP (C:=TYPE) Fib f <-> ∃ (g: B -> sigT (fiber f)), g o f ≡≡ f' f × pr1 o g ≡≡ idmap.
Proof.
  split; intro H.
  - specialize (H (sigT (fiber f)) _ pr1 (Build_IsFibration _ (retract_id _))).
    specialize (H (f' f) idmap E1).
    destruct H as [g [H1 H2]]. exists g. split; apply Eap10; assumption.
  - intros X Y g Hg. ref (LP_Retract (f:=f' f) _ (retract_id _) _).
    use (Build_Retract idmap idmap H.1 pr1); try (intro; reflexivity).
    apply H.2. cbn. symmetry. apply H.2.
    now apply LP_f'_F.
Defined.

Record Cofib {A B} (f : A -> B) := (* C *)
  { cofib_A : Type ;
    cofib_B : Type ;
    cofib_k : cofib_A -> cofib_B ;
    cofib_H : f RetractOf (top' (f:=cofib_k)) }.
Arguments Build_Cofib {A B f A' B'} k H : rename.

(* C are injections into cylinders *)
Definition C_caract {A B} (f: A -> B)
  : LLP (C:=TYPE) AFib f <-> Cofib f.
Proof.
  split.
  - intro Hf. use (Build_Cofib f).
    specialize (Hf (sigT (Cyl f)) B pr1).
    specialize (Hf (Build_AFib (Cyl f) Cyl_Contr (retract_id _))).
    specialize (Hf top' idmap E1).
    destruct Hf as [g [Hg1 Hg2]]; cbn in *.
    use (Build_Retract idmap idmap g pr1); intro; try reflexivity.
    exact (Eap10 Hg2 _). exact (Eap10 Hg1^E _).
  - intros [A' B' f' Hf] A'' B'' g Hg.
    use (LP_Retract Hf (retract_id _)).
      now apply LP_top'_AF.
Defined.

(* C are injections in THEIR cylinders *)
Definition C_caract2 {A B} (f: A -> B)
  : LLP (C:=TYPE) AFib f <-> ∃ (g: B -> sigT (Cyl f)), g o f ≡≡ top' × pr1 o g ≡≡ idmap.
Proof.
  split.
  - intro Hf.
    specialize (Hf (sigT (Cyl f)) B pr1).
    specialize (Hf (Build_AFib (Cyl f) Cyl_Contr (retract_id _))).
    specialize (Hf top' idmap E1).
    destruct Hf as [g [Hg1 Hg2]]; cbn in *.
    exists g; split; now apply Eap10.
  - intros [g [H1 H2]].
    intros A' B' h H.
    ref (LP_Retract (f:=top' (f:=f)) _ (retract_id _) _).
    + use (Build_Retract idmap idmap g pr1); try (intro; reflexivity).
      exact H2. intro; cbn; sym H1.
    + apply LP_top'_AF. assumption.
Defined.           
  
Definition Cofib_W {A B} (f: A -> B)
  : IsEquiv (repl_f (top' (f:=f))) <-> IsEquiv (repl_f f).
Proof.
  assert (H': IsEquiv (repl_f (π1 (Cyl f)))). {
    use isequiv_adjointify. use repl_f. exact base'.
    intro; cbn. rew repl_f_compose; cbn. rew repl_f_idmap. exact 1.
    use repl_ind; cbn. use sig_cyl_ind; cbn.
    intro x. unfold base'. ref (transport (fun y => _ = η (f x; y)) (cyl_eq x) 1).
    intro; exact 1.
    intro; cbn. exact 1. }
  split; intro H.
  - pose proof (isequiv_compose H H').
    cbn in X; rewrite (eq_funext (repl_f_compose _ _)) in X.
    exact X.
  - ref (cancelL_isequiv (repl_f (π1 (Cyl f)))).
    exact H'.
    cbn. rewrite (eq_funext (repl_f_compose top' (π1 (Cyl f)))).
    exact H.
Defined.

Record ACofib {A B} (f : A -> B) := (* AC *)
  { acofib_A : Type ;
    acofib_B : Type ;
    acofib_k : acofib_A -> acofib_B ;
    acofib_Hk : IsEquiv (repl_f acofib_k) ;
    acofib_H : f RetractOf (top' (f:=acofib_k)) }.

Arguments Build_ACofib {A B f A' B'} k Hk H : rename.

(* AC are injections into cylinders of weak equivalences *)
Definition AC_caract2 {A B} (f: A -> B)
  : LLP (C:=TYPE) Fib f <-> ACofib f.
Proof.
  use transitive_iff. 2: apply LLPAFib_ok. split.
  - intros [Hf H].
    ref (Build_ACofib f Hf _).
    specialize (H (sigT (Cyl f)) B pr1).
    assert (AFib (∃ y, Cyl f y) B pr1). {
      ref (Build_AFib _ _ (retract_id _)). 
      cbn. intro y; ref (_ E# Cyl_Contr y).
      apply PFibrant_irrelevance. }
    specialize (H X top' idmap E1); clear X.
    destruct H as [g [H1 H2]]; cbn in *.
    ref (Build_Retract idmap idmap g pr1 _ _ _ _);
      intro; try reflexivity.
    now apply Eap10. exact (Eap10 H1 _)^E.
  - intros [A' B' k Hk H]; split.
    + ref (weak_eq_retract _ _ H _); clear H.
      revert Hk. apply Cofib_W.
    + apply C_caract. ref (Build_Cofib k H).
Defined.


Definition IsInjEq {A B} (f: A -> B)
  := ∃ (r: B -> repl A) (H1: r o f ≡≡ η) (H2: (repl_f f) o r == η),
  forall x, H2 (f x) ≡ Eq_to_paths (Eap (repl_f f) (H1 x)).

(* AC are injective equivalences *)
Definition AC_caract3 {A B} (f: A -> B)
  : LLP (C:=TYPE) Fib f <-> IsInjEq f.
Proof.
  use transitive_iff.
  2: apply AC_caract. split.
  - intros [g [H1 H2]]. exists (λ y, (g y).2.1).
    use exist. intro x. exact (Eap (λ w, w.2.1) (H1 x)).
    use exist. intro y. pose (g y).2.2. cbn in *.
    ref (concat_pE (g y).2.2 _). exact (Eap η (H2 y)).
    intro x; cbn.
    pose (EapD (λ w: sigT (fiber f), w.2.2) (H1 x)^E); cbn in *.
    rewi e; clear e.
    pose (Etransport_paths_FlFrE (f:=λ w, repl_f f w.2.1) (g:= η o pr1) (H1 x)^E E1);
      cbn in *.
    ref (Eap (λ p, concat_pE p (Eap η (H2 (f x)))) _ E@ _).
    2: exact e; clear e.
    ref (concat_pE_ETP _ _ E@ Eap Eq_to_paths (Eq_UIP _ _)).
  - intros [s [H1 [H2 H3]]].
    use exist. ref (fun y => (y; s y; H2 y)).
    split; cbn.
    intro x. ref (eq_sigma _ E1 _); cbn.
    ref (eq_sigma _ (H1 x) _). rew (H3 x).
    ref (Etransport_paths_FlFrE (H1 x) (Eap (repl_f f) (H1 x)) E@ _).
    ref (Eap Eq_to_paths (Eq_UIP _ E1)).
    reflexivity.
Defined.