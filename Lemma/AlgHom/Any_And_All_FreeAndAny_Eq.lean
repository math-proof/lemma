import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


private lemma twist_points
  {B A' H : Type u} [CommRing B] [CommRing A'] [CommRing H] [Algebra B H] [Algebra B A'] :
-- imply
  ∃ τ : ∀ (T : Type u) [CommRing T] [Algebra A' T],
      (A' ⊗[B] H →ₐ[A'] T) ≃ (Subtype fun g : H →+* T => g.comp (algebraMap B H) = (algebraMap A' T).comp (algebraMap B A')),
    ∀ (T T' : Type u) [CommRing T] [Algebra A' T] [CommRing T'] [Algebra A' T'] (u : T →ₐ[A'] T') (f : A' ⊗[B] H →ₐ[A'] T), ((τ T' (u.comp f)).1 : H →+* T') = u.toRingHom.comp (τ T f).1 := by
-- proof
  classical
  let inv : ∀ (T : Type u) [CommRing T] [Algebra A' T],
      (Subtype fun g : H →+* T => g.comp (algebraMap B H) = (algebraMap A' T).comp (algebraMap B A')) → (A' ⊗[B] H →ₐ[A'] T) := fun T _ _ g =>
    let _ : Algebra B T := ((algebraMap A' T).comp (algebraMap B A')).toAlgebra
    let _ : IsScalarTower B A' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Algebra.TensorProduct.lift (Algebra.ofId A' T)
      (AlgHom.mk g.1 (fun b => RingHom.congr_fun g.2 b)) (fun _ _ => Commute.all _ _)
  have inv_tmul : ∀ (T : Type u) [CommRing T] [Algebra A' T] (g : Subtype fun g : H →+* T => g.comp (algebraMap B H) = (algebraMap A' T).comp (algebraMap B A')) (a : A') (h : H), inv T g (a ⊗ₜ h) = algebraMap A' T a * g.1 h := by
    intro T _ _ g a h
    simp [inv, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  refine ⟨fun T _ _ => { toFun := fun f => ⟨f.toRingHom.comp (Algebra.TensorProduct.includeRight : H →ₐ[B] A' ⊗[B] H).toRingHom, ?_⟩, invFun := inv T, left_inv := ?_, right_inv := ?_ }, ?_⟩
  ·
    ext b
    change f (Algebra.TensorProduct.includeRight (algebraMap B H b)) = algebraMap A' T (algebraMap B A' b)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B A' (A' ⊗[B] H), AlgHom.commutes]
  ·
    intro f
    let _ : Algebra B T := ((algebraMap A' T).comp (algebraMap B A')).toAlgebra
    let _ : IsScalarTower B A' T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    apply Algebra.TensorProduct.ext'
    intro a h
    rw [inv_tmul]
    change algebraMap A' T a * f (1 ⊗ₜ h) = f (a ⊗ₜ h)
    rw [← AlgHom.commutes f a, ← map_mul]
    congr 1
    simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  ·
    intro g
    apply Subtype.ext
    ext h
    change inv T g (1 ⊗ₜ h) = g.1 h
    rw [inv_tmul]
    simp
  ·
    intro T T' _ _ _ _ u f
    rfl

private noncomputable def chi
  {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  {d : ℕ} (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')) (i : Fin d) : B →+* A' :=
  (Pi.evalRingHom (fun _ : Fin d => A') i).comp
    (φ.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B).toRingHom)

private lemma chi_apply
  {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  {d : ℕ} {φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')} {i : Fin d} {b : B} :
-- imply
  chi φ i b = φ (1 ⊗ₜ b) i := rfl

private noncomputable def omega
  {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  {d : ℕ} (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A'))
  (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] :
    B ⊗[A] T ≃+* (Fin d → T) :=
  (Algebra.TensorProduct.comm A B T).toRingEquiv.trans <|
    (((Algebra.TensorProduct.cancelBaseChange A A' T T B).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) φ)).trans
        (Algebra.TensorProduct.piScalarRight A' T T (Fin d))).toRingEquiv

private lemma omega_tmul
  {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  {T : Type u} [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T]
  {d : ℕ} {φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')}
  {b : B} {t : T} :
-- imply
  omega φ T (b ⊗ₜ t) = fun i => (chi φ i b) • t := by
-- proof
  simp [omega, chi_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.piScalarRight_tmul]

private lemma omega_algebraMap
  {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  {T : Type u} [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T]
  {d : ℕ} {φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')}
  {b : B} :
-- imply
  omega φ T (algebraMap B (B ⊗[A] T) b) = fun i => algebraMap A' T (chi φ i b) := by
-- proof
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, omega_tmul]
  funext i
  rw [Algebra.smul_def, mul_one]

private lemma omega_map
  {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
  {T : Type u} [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T]
  {T' : Type u} [CommRing T'] [Algebra A T'] [Algebra A' T'] [IsScalarTower A A' T']
  {d : ℕ} {φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')}
  {u : T →ₐ[A'] T'} {x : B ⊗[A] T} :
-- imply
  omega φ T' (Algebra.TensorProduct.map (AlgHom.id B B) (u.restrictScalars A) x) =
    fun i => u (omega φ T x i) := by
-- proof
  induction x using TensorProduct.inductionOn with
  | tmul b t =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.restrictScalars_apply, omega_tmul, omega_tmul]
    funext i
    rw [map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    funext i
    simp [map_add]

private lemma lhs_points
  {A B A' H : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing H] [Algebra A B] [Algebra A A'] [Algebra B H]
  {d : ℕ} {φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')} :
-- imply
  ∃ ρ : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
      (H →ₐ[B] (B ⊗[A] T)) ≃ (Subtype fun g : Fin d → (H →+* T) => ∀ i, (g i).comp (algebraMap B H) = (algebraMap A' T).comp (chi φ i)),
    ∀ (T T' : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] [CommRing T'] [Algebra A T'] [Algebra A' T'] [IsScalarTower A A' T'] (u : T →ₐ[A'] T') (g : H →ₐ[B] (B ⊗[A] T)) (i : Fin d),
      (ρ T' ((Algebra.TensorProduct.map (AlgHom.id B B) (u.restrictScalars A)).comp g)).1 i =
        u.toRingHom.comp ((ρ T g).1 i) := by
-- proof
  classical
  let fwd : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
      (H →ₐ[B] (B ⊗[A] T)) → Fin d → (H →+* T) := fun T _ _ _ _ g i =>
    (Pi.evalRingHom (fun _ : Fin d => T) i).comp ((omega φ T).toRingHom.comp g.toRingHom)
  have fwd_apply : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] (g : H →ₐ[B] (B ⊗[A] T)) (i : Fin d) (h : H), fwd T g i h = omega φ T (g h) i := by
    intro T _ _ _ _ g i h
    rfl
  have fwd_prop : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] (g : H →ₐ[B] (B ⊗[A] T)) (i : Fin d), (fwd T g i).comp (algebraMap B H) = (algebraMap A' T).comp (chi φ i) := by
    intro T _ _ _ _ g i
    ext b
    change fwd T g i (algebraMap B H b) = algebraMap A' T (chi φ i b)
    rw [fwd_apply, AlgHom.commutes, omega_algebraMap]
  let bwd : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
      (Subtype fun g : Fin d → (H →+* T) => ∀ i, (g i).comp (algebraMap B H) = (algebraMap A' T).comp (chi φ i)) → (H →ₐ[B] (B ⊗[A] T)) := fun T _ _ _ _ g =>
    AlgHom.mk ((omega φ T).symm.toRingHom.comp (RingHom.pi g.1)) (fun b => by change (omega φ T).symm (fun i => g.1 i (algebraMap B H b)) = algebraMap B (B ⊗[A] T) b; rw [RingEquiv.symm_apply_eq, omega_algebraMap]; funext i; apply RingHom.congr_fun (g.2 i) b)
  have bwd_apply : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] (g : Subtype fun g : Fin d → (H →+* T) => ∀ i, (g i).comp (algebraMap B H) = (algebraMap A' T).comp (chi φ i)) (h : H), bwd T g h = (omega φ T).symm (fun i => g.1 i h) := by
    intro T _ _ _ _ g h
    rfl
  refine ⟨fun T _ _ _ _ => { toFun := fun g => ⟨fwd T g, fwd_prop T g⟩, invFun := bwd T, left_inv := ?_, right_inv := ?_ }, ?_⟩
  ·
    intro g
    apply AlgHom.ext
    intro h
    rw [bwd_apply, RingEquiv.symm_apply_eq]
    funext i
    apply (fwd_apply T g i h).symm
  ·
    intro g
    apply Subtype.ext
    funext i
    ext h
    change fwd T (bwd T g) i h = g.1 i h
    rw [fwd_apply, bwd_apply, RingEquiv.apply_symm_apply]
  ·
    intro T T' _ _ _ _ _ _ _ _ u g i
    ext h
    change fwd T' _ i h = u (fwd T g i h)
    rw [fwd_apply, fwd_apply, AlgHom.comp_apply, omega_map]


/--
[Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_finite_free_algHom_tensorProduct_equiv_pi_of_algEquiv_pi.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A]
  {B : Type u} [CommRing B] [Algebra A B]
  {H : Type u} [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
  {A' : Type u} [CommRing A'] [Algebra A A']
  {d : ℕ}
  {φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')} :
-- imply
  ∃ (F : Fin d → Type u) (_ : ∀ i, CommRing (F i)) (_ : ∀ i, Algebra A' (F i)),
    (∀ i, Module.Finite A' (F i)) ∧ (∀ i, Module.Free A' (F i)) ∧
    ∃ σ : ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T],
        (H →ₐ[B] (B ⊗[A] T)) ≃ (∀ i, F i →ₐ[A'] T),
      ∀ (T T' : Type u) [CommRing T] [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] [CommRing T'] [Algebra A T'] [Algebra A' T'] [IsScalarTower A A' T'] (u : T →ₐ[A'] T') (g : H →ₐ[B] (B ⊗[A] T)),
        σ T' ((Algebra.TensorProduct.map (AlgHom.id B B) (u.restrictScalars A)).comp g)
          = fun i => u.comp (σ T g i) := by
-- proof
  classical
  obtain ⟨ρ, hρ⟩ := lhs_points (A := A) (B := B) (A' := A') (H := H) (φ := φ)
  have hτ := fun i : Fin d =>
    @twist_points B A' H _ _ _ _ ((chi φ i).toAlgebra)
  choose τ hτ using hτ
  refine ⟨fun i => @TensorProduct B _ A' H _ _ ((chi φ i).toAlgebra).toModule _, fun i => by let _ := (chi φ i).toAlgebra; infer_instance, fun i => by let _ := (chi φ i).toAlgebra; infer_instance, fun i => by let _ := (chi φ i).toAlgebra; infer_instance, fun i => by let _ := (chi φ i).toAlgebra; infer_instance, fun T _ _ _ _ => (ρ T).trans (Equiv.subtypePiEquivPi.trans (Equiv.piCongrRight fun i => (τ i T).symm)), ?_⟩
  intro T T' _ _ _ _ _ _ _ _ u g
  funext i
  show (τ i T').symm _ = _
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  rw [hτ]
  simp [Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply, Equiv.apply_symm_apply]
  apply hρ T T' u g i


-- created on 2026-10-16
