import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private abbrev Chart (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A] : Type :=
  Subtype fun (N : Module.Grassmannian A (A ⊗[R] M) k) => Function.Bijective fun v : Fin k → A => ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)

private abbrev HomX (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) (A : Type) [CommRing A] [Algebra R A] : Type :=
  Subtype fun (ψ : M →ₗ[R] (Fin k → A)) => ∀ j, ψ (x j) = Pi.single j 1

private noncomputable def cmap {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Submodule A (A ⊗[R] M)) : (Fin k → A) →ₗ[A] (A ⊗[R] M) ⧸ N :=
  Fintype.linearCombination A (fun i => N.mkQ ((1 : A) ⊗ₜ[R] x i))

private lemma coe_cmap {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Submodule A (A ⊗[R] M)) : ⇑(cmap x N) = fun v : Fin k → A => ∑ i, v i • N.mkQ ((1 : A) ⊗ₜ[R] x i) := rfl

private lemma cmap_single {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Submodule A (A ⊗[R] M)) (j : Fin k) : cmap x N (Pi.single j 1) = N.mkQ ((1 : A) ⊗ₜ[R] x j) := by
  classical
  simp [cmap]

private noncomputable def coordEquiv {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) : (Fin k → A) ≃ₗ[A] (A ⊗[R] M) ⧸ N.1.toSubmodule :=
  LinearEquiv.ofBijective (cmap x N.1.toSubmodule) N.2

private lemma coordEquiv_apply {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) (v : Fin k → A) : coordEquiv x N v = cmap x N.1.toSubmodule v := rfl

private lemma coordEquiv_symm_mkQ_x {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) (j : Fin k) : (coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x j)) = Pi.single j 1 := by
  rw [LinearEquiv.symm_apply_eq, coordEquiv_apply, cmap_single]

private noncomputable def toHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) : HomX R x A :=
  ⟨LinearMap.comp ((LinearMap.comp (coordEquiv x N).symm.toLinearMap N.1.toSubmodule.mkQ).restrictScalars R) (TensorProduct.mk R A M 1),
    fun j => by
      simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.mk_apply]
      exact coordEquiv_symm_mkQ_x x N j⟩

private lemma toHomX_apply {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) (m : M) : (toHomX x N).1 m = (coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) := rfl

private abbrev ext' {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} {A : Type} [CommRing A] [Algebra R A] (ψ : M →ₗ[R] (Fin k → A)) : A ⊗[R] M →ₗ[A] (Fin k → A) :=
  ψ.liftBaseChange A

private lemma ext'_surjective {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) : Function.Surjective (ext' ψ.1) := by
  intro v
  refine ⟨∑ i, v i ⊗ₜ[R] x i, ?_⟩
  simp only [map_sum, LinearMap.liftBaseChange_tmul, ψ.2]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

private noncomputable def quotEquiv {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) : ((A ⊗[R] M) ⧸ LinearMap.ker (ext' ψ.1)) ≃ₗ[A] (Fin k → A) :=
  (ext' ψ.1).quotKerEquivOfSurjective (ext'_surjective x ψ)

private lemma quotEquiv_mkQ {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) (p : A ⊗[R] M) : quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ p) = ext' ψ.1 p :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

private lemma quotEquiv_cmap {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) (v : Fin k → A) : quotEquiv x ψ (cmap x (LinearMap.ker (ext' ψ.1)) v) = v := by
  simp only [coe_cmap, map_sum, map_smul, quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul, ψ.2]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

private lemma cmap_ker_eq {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) : ⇑(cmap x (LinearMap.ker (ext' ψ.1))) = (quotEquiv x ψ).symm := by
  funext v
  rw [eq_comm, LinearEquiv.symm_apply_eq, quotEquiv_cmap]

private noncomputable def ofHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) : Chart R x A := by
  refine ⟨{ toSubmodule := LinearMap.ker (ext' ψ.1)
            finite_quotient := Module.Finite.equiv (quotEquiv x ψ).symm
            projective_quotient := Module.Projective.of_equiv (quotEquiv x ψ).symm
            rankAtStalk_eq := fun p => ?_ }, ?_⟩
  ·
    have : Nontrivial A := by
      by_contra h
      let _ := not_nontrivial_iff_subsingleton.mp h
      exact IsEmpty.false p
    rw [Module.rankAtStalk_eq_of_equiv (quotEquiv x ψ), Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun]
    rfl
  ·
    change Function.Bijective (cmap x (LinearMap.ker (ext' ψ.1)))
    rw [cmap_ker_eq]
    refine (quotEquiv x ψ).symm.bijective

private lemma ofHomX_toSubmodule {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) : (ofHomX x ψ).1.toSubmodule = LinearMap.ker (ext' ψ.1) := rfl

private lemma ext'_toHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) : ext' (toHomX x N).1 = LinearMap.comp (coordEquiv x N).symm.toLinearMap N.1.toSubmodule.mkQ := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  simp only [LinearMap.liftBaseChange_tmul, toHomX_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private lemma ofHomX_toHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (N : Chart R x A) : ofHomX x (toHomX x N) = N := by
  apply Subtype.ext
  apply Module.Grassmannian.ext
  rw [ofHomX_toSubmodule, ext'_toHomX, LinearEquiv.ker_comp, Submodule.ker_mkQ]

private lemma coordEquiv_ofHomX_symm {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) (y : (A ⊗[R] M) ⧸ LinearMap.ker (ext' ψ.1)) : (coordEquiv x (ofHomX x ψ)).symm y = quotEquiv x ψ y := by
  have h1 : (coordEquiv x (ofHomX x ψ)) ((coordEquiv x (ofHomX x ψ)).symm y) = y := LinearEquiv.apply_symm_apply _ _
  rw [coordEquiv_apply] at h1
  have h2 := congrArg (quotEquiv x ψ) h1
  change quotEquiv x ψ (cmap x (LinearMap.ker (ext' ψ.1)) _) = _ at h2
  rwa [quotEquiv_cmap] at h2

private lemma toHomX_ofHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] (ψ : HomX R x A) : toHomX x (ofHomX x ψ) = ψ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  rw [toHomX_apply, coordEquiv_ofHomX_symm]
  change quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ ((1 : A) ⊗ₜ[R] m)) = _
  rw [quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul]

private noncomputable def chartEquiv {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] : Chart R x A ≃ HomX R x A where
  toFun := toHomX x
  invFun := ofHomX x
  left_inv := ofHomX_toHomX x
  right_inv := toHomX_ofHomX x

private noncomputable def pushHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (ψ : HomX R x A) : HomX R x B :=
  ⟨LinearMap.comp (φ.toLinearMap.compLeft (Fin k)) ψ.1, fun j => by
    ext i
    simp [LinearMap.compLeft, ψ.2, Pi.single_apply, apply_ite φ]⟩

private lemma pushHomX_apply {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (ψ : HomX R x A) (m : M) (i : Fin k) : (pushHomX x φ ψ).1 m i = φ (ψ.1 m i) := rfl

private lemma map_ofHomX_toSubmodule {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (ψ : HomX R x A) : (Module.Grassmannian.map φ (ofHomX x ψ).1).toSubmodule = LinearMap.ker (ext' (pushHomX x φ ψ).1) := by
  classical
  rw [Module.Grassmannian.map_toSubmodule]
  let _ : Algebra A B := φ.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B
  let T : B ⊗[A] ((A ⊗[R] M) ⧸ (ofHomX x ψ).1.toSubmodule) ≃ₗ[B] (Fin k → B) := ((quotEquiv x ψ).baseChange A B _ _).trans (TensorProduct.piScalarRight A B B (Fin k))
  have hT : LinearMap.comp T.toLinearMap (Module.Grassmannian.baseChangeMkQ B (ofHomX x ψ).1.toSubmodule) = ext' (pushHomX x φ ψ).1 := by
    refine TensorProduct.AlgebraTensorModule.ext fun b m => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.Grassmannian.baseChangeMkQ, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    simp only [T, LinearEquiv.trans_apply]
    change TensorProduct.piScalarRight A B B (Fin k) (b ⊗ₜ[A] quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ _)) = _
    rw [quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul]
    ext i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Pi.smul_apply, pushHomX_apply, smul_eq_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    rfl
  rw [← hT, LinearEquiv.ker_comp]

private lemma map_ofHomX {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (ψ : HomX R x A) : Module.Grassmannian.map φ (ofHomX x ψ).1 = (ofHomX x (pushHomX x φ ψ)).1 :=
  Module.Grassmannian.ext (map_ofHomX_toSubmodule x φ ψ)

private lemma map_mem_chart {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (N : Chart R x A) : Function.Bijective fun v : Fin k → B => ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i) := by
  have hN : N = ofHomX x (toHomX x N) := (ofHomX_toHomX x N).symm
  rw [hN, map_ofHomX]
  refine (ofHomX x (pushHomX x φ (toHomX x N))).2

private lemma chartEquiv_map {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M) {A : Type} [CommRing A] [Algebra R A] {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (N : Chart R x A) : chartEquiv x ⟨Module.Grassmannian.map φ N.1, map_mem_chart x φ N⟩ = pushHomX x φ (chartEquiv x N) := by
  have hN : N = ofHomX x (toHomX x N) := (ofHomX_toHomX x N).symm
  have : (⟨Module.Grassmannian.map φ N.1, map_mem_chart x φ N⟩ : Chart R x B) = ofHomX x (pushHomX x φ (toHomX x N)) := by
    apply Subtype.ext
    change Module.Grassmannian.map φ N.1 = _
    conv_lhs => rw [hN]
    exact map_ofHomX x φ (toHomX x N)
  rw [this]
  refine toHomX_ofHomX x _

/--
[Module_Grassmannian_exists_chart_equiv_linearMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Grassmannian_exists_chart_equiv_linearMap.lean)
-/
@[path]
private lemma main
  (R : Type) [CommRing R]
  (M : Type) [AddCommGroup M] [Module R M]
  (k : ℕ)
  (x : Fin k → M) :
  -- imply
  ∃ pt : ∀ (A : Type) [CommRing A] [Algebra R A], Chart R x A ≃ HomX R x A,
    (∀ (A : Type) [CommRing A] [Algebra R A] (N : Chart R x A) (m : M), ∑ i, (pt A N).1 m i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) = N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
    (∀ (A : Type) [CommRing A] [Algebra R A] (ψ : HomX R x A), ((pt A).symm ψ).1.toSubmodule = LinearMap.ker (ψ.1.liftBaseChange A)) ∧
    (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) (N : Chart R x A), ∃ h : Function.Bijective fun v : Fin k → B => ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i), ∀ (m : M) (i : Fin k), (pt B ⟨Module.Grassmannian.map φ N.1, h⟩).1 m i = φ ((pt A N).1 m i)) := by
  -- proof
  refine ⟨fun A _ _ => chartEquiv (R := R) (A := A) x, ?_, ?_, ?_⟩
  ·
    intro A _ _ N m
    change cmap x N.1.toSubmodule ((coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m))) = _
    rw [← coordEquiv_apply, LinearEquiv.apply_symm_apply]
  ·
    intro A _ _ ψ
    rfl
  ·
    intro A B _ _ _ _ φ N
    exact ⟨map_mem_chart x φ N, fun m i => congrArg (fun ψ : HomX R x B => ψ.1 m i) (chartEquiv_map x φ N)⟩


-- created on 2026-10-20
