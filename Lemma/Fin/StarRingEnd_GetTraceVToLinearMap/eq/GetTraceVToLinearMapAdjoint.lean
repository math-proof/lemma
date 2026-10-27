import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.SchurOrthogonalityConsequences
open MeasureTheory ContinuousRep
open scoped ComplexConjugate


/--
[conj_trace_clm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonalityConsequences.lean)
-/
@[path]
private lemma main
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [NormedAddCommGroup V]
  [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]
  [CompleteSpace V]
  {f : V →L[ℂ] V} :
-- imply
  starRingEnd ℂ ((LinearMap.trace ℂ V) f.toLinearMap) = (LinearMap.trace ℂ V) (ContinuousLinearMap.adjoint f).toLinearMap := by
-- proof
  let b := stdOrthonormalBasis ℂ V
  rw [LinearMap.trace_eq_sum_inner f.toLinearMap b,
    LinearMap.trace_eq_sum_inner (ContinuousLinearMap.adjoint f).toLinearMap b]
  simp only [ContinuousLinearMap.coe_coe, map_sum]
  congr 1; ext i; rw [inner_conj_symm]
  exact (ContinuousLinearMap.adjoint_inner_right f (b i) (b i)).symm

/--
[adjoint_comp_endo](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonalityConsequences.lean)
-/
private lemma adjoint_comp_endo
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [NormedAddCommGroup V]
  [InnerProductSpace ℂ V]
  [CompleteSpace V]
  {f g : V →L[ℂ] V} :
-- imply
  ContinuousLinearMap.adjoint (f.comp g) = (ContinuousLinearMap.adjoint g).comp (ContinuousLinearMap.adjoint f) := by
-- proof
  ext x; apply @ext_inner_right ℂ; intro y
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

/--
[unitary_inv_eq_adjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonalityConsequences.lean)
-/
private lemma unitary_inv_eq_adjoint
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [Group G]
  [NormedAddCommGroup W]
  [InnerProductSpace ℂ W]
  [CompleteSpace W]
  {ρ_hom : G →* (W →L[ℂ] W)}
  {g : G}
-- given
  (hU : ∀ g, ContinuousLinearMap.adjoint (ρ_hom g) * (ρ_hom g) = 1 ∧ (ρ_hom g) * ContinuousLinearMap.adjoint (ρ_hom g) = 1) :
-- imply
  ρ_hom g⁻¹ = ContinuousLinearMap.adjoint (ρ_hom g) := by
-- proof
  have h1 : ρ_hom g⁻¹ * ρ_hom g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc ρ_hom g⁻¹ = ρ_hom g⁻¹ * (ρ_hom g * ContinuousLinearMap.adjoint (ρ_hom g)) := by
    rw [(hU g).2, mul_one]
    _ = (ρ_hom g⁻¹ * ρ_hom g) * ContinuousLinearMap.adjoint (ρ_hom g) := by rw [mul_assoc]
    _ = ContinuousLinearMap.adjoint (ρ_hom g) := by rw [h1, one_mul]

/--
[key_trace_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurOrthogonalityConsequences.lean)
-/
private lemma key_trace_identity
  [Group K]
  [TopologicalSpace K]
  [IsTopologicalGroup K]
  [Group G]
  [NormedAddCommGroup W]
  [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]
  [CompleteSpace W]
  {ρ_hom : G →* (W →L[ℂ] W)}
  {A : W →L[ℂ] W}
  {z y : G}
-- given
  (hU : ∀ g, ContinuousLinearMap.adjoint (ρ_hom g) * (ρ_hom g) = 1 ∧ (ρ_hom g) * ContinuousLinearMap.adjoint (ρ_hom g) = 1) :
-- imply
  (LinearMap.trace ℂ W) (A.comp (ρ_hom (z * y⁻¹))).toLinearMap = starRingEnd ℂ ((LinearMap.trace ℂ W) ((ContinuousLinearMap.adjoint (A.comp (ρ_hom z))).comp (ρ_hom y)).toLinearMap) := by
-- proof
  have h_inv : ρ_hom y⁻¹ = ContinuousLinearMap.adjoint (ρ_hom y) :=
    unitary_inv_eq_adjoint ρ_hom hU y
  have h_lhs_eq : A.comp (ρ_hom (z * y⁻¹)) =
    (A.comp (ρ_hom z)).comp (ContinuousLinearMap.adjoint (ρ_hom y)) := by
    have : ρ_hom (z * y⁻¹) = (ρ_hom z).comp (ρ_hom y⁻¹) := by ext v; simp [map_mul]
    rw [this, h_inv]; ext; simp
  rw [h_lhs_eq, conj_trace_clm, adjoint_comp_endo, ContinuousLinearMap.adjoint_adjoint]
  change (LinearMap.trace ℂ W) ((A.comp (ρ_hom z)).toLinearMap.comp
    (ContinuousLinearMap.adjoint (ρ_hom y)).toLinearMap) =
    (LinearMap.trace ℂ W) ((ContinuousLinearMap.adjoint (ρ_hom y)).toLinearMap.comp
      (A.comp (ρ_hom z)).toLinearMap)
  exact LinearMap.trace_comp_comm' (ContinuousLinearMap.adjoint (ρ_hom y)).toLinearMap
    (A.comp (ρ_hom z)).toLinearMap
section MatrixCoefficientDensity
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]


-- created on 2026-10-23
-- updated on 2026-10-26
