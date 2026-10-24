import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_HopfAlgebra_HopfKer
open scoped TensorProduct


private lemma helper_main
  {R : Type u} [CommRing R] (R₁ : Type u) [CommRing R₁] [Algebra R R₁] [Module.Flat R R₁]
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  {H' : Type w} [CommRing H'] [HopfAlgebra R H']
  (qc : BialgHom R H H') :
  Subalgebra.toSubmodule
    (HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
      BialgHom R₁ (R₁ ⊗[R] H) (R₁ ⊗[R] H'))) = LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange R₁) := by
  classical
  set qc₁ : BialgHom R₁ (R₁ ⊗[R] H) (R₁ ⊗[R] H') := Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc
    with hqc₁
  let D : H →ₗ[R] H ⊗[R] H' :=
    (HopfAlgebra.coaction qc).toLinearMap - (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H').toLinearMap
  have hD : ∀ a, D a = HopfAlgebra.coaction qc a - a ⊗ₜ[R] 1 := fun a => rfl
  have hexact : Function.Exact (HopfAlgebra.hopfKer qc).val.toLinearMap D := by
    rw [LinearMap.exact_iff]
    ext a
    rw [LinearMap.mem_ker, hD, sub_eq_zero, LinearMap.mem_range]
    constructor
    ·
      intro ha
      exact ⟨⟨a, (HopfAlgebra.mem_hopfKer_iff qc a).mpr ha⟩, rfl⟩
    ·
      rintro ⟨k, rfl⟩
      exact (HopfAlgebra.mem_hopfKer_iff qc _).mp k.2
  have hker₁ : LinearMap.ker (D.lTensor R₁) =
      LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.lTensor R₁) :=
    LinearMap.exact_iff.mp (Module.Flat.lTensor_exact R₁ hexact)
  let Θ : (R₁ ⊗[R] H) ⊗[R₁] (R₁ ⊗[R] H') ≃ₗ[R₁] R₁ ⊗[R] (H ⊗[R] H') :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R₁ R₁ (R₁ ⊗[R] H) H').trans
      (TensorProduct.AlgebraTensorModule.assoc R R R₁ R₁ H H')
  have hΘ : ∀ (r s : R₁) (h : H) (h' : H'),
      Θ ((r ⊗ₜ[R] h) ⊗ₜ[R₁] (s ⊗ₜ[R] h')) = (s * r) ⊗ₜ[R] (h ⊗ₜ[R] h') := by
    intro r s h h'
    show TensorProduct.AlgebraTensorModule.assoc R R R₁ R₁ H H'
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R R₁ R₁ (R₁ ⊗[R] H) H'
        ((r ⊗ₜ[R] h) ⊗ₜ[R₁] (s ⊗ₜ[R] h'))) = (s * r) ⊗ₜ[R] (h ⊗ₜ[R] h')
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      TensorProduct.AlgebraTensorModule.assoc_tmul]
  let ΘR : (R₁ ⊗[R] H) ⊗[R₁] (R₁ ⊗[R] H') →ₗ[R] R₁ ⊗[R] (H ⊗[R] H') := Θ.toLinearMap.restrictScalars R
  have hΘR : ∀ z, ΘR z = Θ z := fun _ => rfl
  have hco_lin : ΘR.comp ((HopfAlgebra.coaction qc₁).toLinearMap.restrictScalars R) = (HopfAlgebra.coaction qc).toLinearMap.lTensor R₁ := by
    refine TensorProduct.ext' fun r h => ?_
    show Θ (HopfAlgebra.coaction qc₁ (r ⊗ₜ[R] h)) = (HopfAlgebra.coaction qc).toLinearMap.lTensor R₁ (r ⊗ₜ[R] h)
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, HopfAlgebra.coaction_apply,
      HopfAlgebra.coaction_apply, TensorProduct.comul_tmul, CommSemiring.comul_apply]
    let L₁ : H ⊗[R] H →ₗ[R] R₁ ⊗[R] (H ⊗[R] H') :=
      ΘR.comp ((Algebra.TensorProduct.map (AlgHom.id R₁ (R₁ ⊗[R] H)) (qc₁ : R₁ ⊗[R] H →ₐ[R₁] R₁ ⊗[R] H')).toLinearMap.restrictScalars R)
        .comp ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R₁ R R₁ R₁ R₁ H H).toLinearMap.restrictScalars R)
        .comp (TensorProduct.mk R (R₁ ⊗[R₁] R₁) (H ⊗[R] H) ((1 : R₁) ⊗ₜ[R₁] r))
    let L₂ : H ⊗[R] H →ₗ[R] R₁ ⊗[R] (H ⊗[R] H') :=
      (TensorProduct.mk R R₁ (H ⊗[R] H') r).comp ((Algebra.TensorProduct.map (AlgHom.id R H) (qc : H →ₐ[R] H')).toLinearMap)
    have hL : L₁ = L₂ := by
      refine TensorProduct.ext' fun a b => ?_
      show Θ (Algebra.TensorProduct.map (AlgHom.id R₁ (R₁ ⊗[R] H)) (qc₁ : R₁ ⊗[R] H →ₐ[R₁] R₁ ⊗[R] H')
          (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R₁ R R₁ R₁ R₁ H H
            (((1 : R₁) ⊗ₜ[R₁] r) ⊗ₜ[R] (a ⊗ₜ[R] b)))) = r ⊗ₜ[R] (Algebra.TensorProduct.map (AlgHom.id R H) (qc : H →ₐ[R] H') (a ⊗ₜ[R] b))
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply]
      show Θ ((1 ⊗ₜ[R] a) ⊗ₜ[R₁] (qc₁ (r ⊗ₜ[R] b))) = r ⊗ₜ[R] (a ⊗ₜ[R] qc b)
      rw [hqc₁, Bialgebra.TensorProduct.map_tmul, hΘ, mul_one]
      rfl
    refine LinearMap.congr_fun hL (Coalgebra.comul (R := R) h)
  have hco : ∀ x : R₁ ⊗[R] H,
      Θ (HopfAlgebra.coaction qc₁ x) = (HopfAlgebra.coaction qc).toLinearMap.lTensor R₁ x :=
    fun x => LinearMap.congr_fun hco_lin x
  have hone_lin : ΘR.comp (((TensorProduct.mk R₁ (R₁ ⊗[R] H) (R₁ ⊗[R] H')).flip (1 : R₁ ⊗[R] H')).restrictScalars R) = (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H').toLinearMap.lTensor R₁ := by
    refine TensorProduct.ext' fun r h => ?_
    show Θ ((r ⊗ₜ[R] h) ⊗ₜ[R₁] (1 : R₁ ⊗[R] H')) = _
    rw [Algebra.TensorProduct.one_def, hΘ, one_mul, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.includeLeft_apply]
  have hone : ∀ x : R₁ ⊗[R] H,
      Θ (x ⊗ₜ[R₁] (1 : R₁ ⊗[R] H')) =
        (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H').toLinearMap.lTensor R₁ x :=
    fun x => LinearMap.congr_fun hone_lin x
  ext x
  rw [Subalgebra.mem_toSubmodule, HopfAlgebra.mem_hopfKer_iff, LinearMap.mem_range]
  constructor
  ·
    intro hx
    have hmem : x ∈ LinearMap.ker (D.lTensor R₁) := by
      rw [LinearMap.mem_ker, LinearMap.lTensor_sub, LinearMap.sub_apply, ← hco, ← hone, hx, sub_self]
    rw [hker₁, LinearMap.mem_range] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, (congrFun (LinearMap.baseChange_eq_ltensor _) y).trans hy⟩
  ·
    rintro ⟨y, rfl⟩
    apply Θ.injective
    rw [hco, hone]
    have hmem : (HopfAlgebra.hopfKer qc).val.toLinearMap.lTensor R₁ y ∈ LinearMap.ker (D.lTensor R₁) := by
      rw [hker₁]; exact ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero] at hmem
    rwa [congrFun (LinearMap.baseChange_eq_ltensor _) y]
/--
[HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {R₁ : Type u} [CommRing R₁] [Algebra R R₁] [Module.Flat R R₁]
  {H : Type v} [CommRing H] [HopfAlgebra R H]
  {H' : Type w} [CommRing H'] [HopfAlgebra R H']
  {qc : BialgHom R H H'} :
-- imply
  Subalgebra.toSubmodule
    (HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
      BialgHom R₁ (R₁ ⊗[R] H) (R₁ ⊗[R] H'))) = LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange R₁) :=
-- proof
  helper_main R₁ qc


-- created on 2026-10-23
