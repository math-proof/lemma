import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW
open Manifold


/--
[posdef_signature_eq_b₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma posdef_signature_eq_b₂ (Q : IntersectionForm) (hdef : Q.IsPositiveDefinite) :
  Q.signature = (Q.b₂ : ℤ) := by
  rw [Q.signature_eq, Q.rank_decomp]; unfold IntersectionForm.IsPositiveDefinite at hdef; simp [hdef]

/--
[negdef_signature_eq_neg_b₂](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma negdef_signature_eq_neg_b₂ (Q : IntersectionForm) (hdef : Q.IsNegativeDefinite) :
  Q.signature = -((Q.b₂ : ℤ)) := by
  rw [Q.signature_eq, Q.rank_decomp]; unfold IntersectionForm.IsNegativeDefinite at hdef; simp [hdef]

/--
[SWSolution.weitzenbock_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SWSolution.weitzenbock_decomp
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  sol.diracSqInnerProd = sol.connLapInnerProd + (sol.scalarCurvatureVal / 4) * sol.supNormSq + (1 / 2) * sol.cliffordInnerProd := by
-- proof
  have h_split := sol.diracSq_split
  have h_diag := sol.diagonal_eq
  have h_offdiag := sol.offdiagonal_eq
  linarith

/--
[SWSolution.weitzenbock_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SWSolution.weitzenbock_eq
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  0 = sol.connLapInnerProd + (sol.scalarCurvatureVal / 4) * sol.supNormSq + (1 / 2) * sol.cliffordInnerProd := by
-- proof
  have h1 := sol.weitzenbock_decomp
  have h2 := sol.dirac_kernel
  linarith

/--
[SWSolution.bochner_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SWSolution.bochner_eq
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  sol.laplacianTerm + sol.covDerivNormSq + (sol.scalarCurvatureVal / 4) * sol.supNormSq + (1/4) * sol.supNormSq ^ 2 = 0 := by
-- proof
  have hW := sol.weitzenbock_eq
  have hIBP := sol.integration_by_parts_eq
  have hCurv := sol.clifford_quadratic_eq
  linarith

/--
[clifford_quadratic_from_curvature](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma clifford_quadratic_from_curvature
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  spinc.hermitianInnerPlus (spinc.γ_on_2forms sol.F_A_plus sol.ψ) sol.ψ = (1 / 2) * sol.supNormSq ^ 2 := by
-- proof
  rw [sol.curvature_eq_applied]
  unfold SpinCStructure.tracelessQuadratic
  have h_norm := spinc.hermitian_norm_compat sol.ψ
  rw [h_norm, sol.supNormSq_eq]
  have h_sub : spinc.normSqPlus sol.ψ • sol.ψ - (1 / 2 * spinc.normSqPlus sol.ψ) • sol.ψ =
    (1 / 2 * spinc.normSqPlus sol.ψ) • sol.ψ := by
    rw [← sub_smul]; congr 1; ring
  rw [h_sub]
  rw [spinc.hermitian_smul_left]
  rw [spinc.hermitian_norm_compat]
  ring

/--
[SWSolution.clifford_quadratic_derived](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SWSolution.clifford_quadratic_derived
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  sol.cliffordInnerProd = (1 / 2) * sol.supNormSq ^ 2 := by
-- proof
  rw [sol.clifford_inner_from_gamma]
  exact clifford_quadratic_from_curvature sol

/--
[SWSolution.isReducible_iff_supNormSq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SWSolution.isReducible_iff_supNormSq_zero
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc} :
-- imply
  sol.isReducible ↔ sol.supNormSq = 0 := by
-- proof
  unfold SWSolution.isReducible
  rw [sol.supNormSq_eq]
  exact (spinc.normSq_zero_iff sol.ψ).symm
section SWEquations
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (𝓡 4) ⊤ M]
variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
variable {spinc : SpinCStructure M Ω1 Ω2}
variable [Zero spinc.SectionsMinus]

/--
[IsSWSolution.toPerturbed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma IsSWSolution.toPerturbed
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  [Zero spinc.SectionsMinus]
  {sol : SWSolution spinc}
-- given
  (h : IsSWSolution sol)
  (hγ_zero : ∀ (φ : spinc.SectionsPlus), spinc.γ_on_2forms (0 : Ω2) φ = 0) :
-- imply
  IsSWSolutionWith sol (0 : Ω2) where dirac_eq :=
-- proof
  h.dirac_eq
    curvature_eq := fun φ => by
      simp only [hγ_zero φ, add_zero]
      exact h.curvature_eq φ

/--
[IsSWSolution.ofPerturbed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma IsSWSolution.ofPerturbed
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  [Zero spinc.SectionsMinus]
  {sol : SWSolution spinc}
-- given
  (h : IsSWSolutionWith sol (0 : Ω2))
  (hγ_zero : ∀ (φ : spinc.SectionsPlus), spinc.γ_on_2forms (0 : Ω2) φ = 0) :
-- imply
  IsSWSolution sol where dirac_eq :=
-- proof
  h.dirac_eq
    curvature_eq := fun φ => by
      have := h.curvature_eq φ
      simp only [hγ_zero φ, add_zero] at this
      exact this

/--
[IsSWSolutionWith.dirac_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma IsSWSolutionWith.dirac_vanishes
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  [Zero spinc.SectionsMinus]
  {sol : SWSolution spinc}
  {μ : Ω2}
-- given
  (h : IsSWSolutionWith sol μ) :
-- imply
  sol.dirac.D_plus sol.ψ = 0 :=
-- proof
  h.dirac_eq

/--
[IsSWSolutionWith.ofIsSWSolution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma IsSWSolutionWith.ofIsSWSolution
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  [Zero spinc.SectionsMinus]
  {sol : SWSolution spinc}
  {μ : Ω2}
-- given
  (h_dirac : sol.dirac.D_plus sol.ψ = 0)
  (h_curv : ∀ (φ : spinc.SectionsPlus), spinc.γ_on_2forms sol.F_A_plus φ = spinc.tracelessQuadratic sol.ψ φ + spinc.γ_on_2forms μ φ) :
-- imply
  IsSWSolutionWith sol μ where dirac_eq :=
-- proof
  h_dirac
    curvature_eq := h_curv
end SWEquations

/--
[GaugeActionData.free_iff_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma GaugeActionData.free_iff_irreducible
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gauge : GaugeActionData spinc}
  {sol : SWSolution spinc}
  {f : gauge.GaugeGroup}
-- given
  (hirr : ¬sol.isReducible)
  (hfix : gauge.gauge_action f sol = sol) :
-- imply
  f = 1 :=
-- proof
  gauge.gauge_free_on_irreducible sol hirr f hfix

/--
[SmoothGaugeGroup.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SmoothGaugeGroup.ext
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  {f g : SmoothGaugeGroup M}
-- given
  (h : f.1 = g.1) :
-- imply
  f = g :=
-- proof
  Subtype.ext h

/--
[SWModuliQuotient.eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma SWModuliQuotient.eq_iff
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gd : GaugeActionData spinc}
  {sol₁ sol₂ : SWSolution spinc} :
-- imply
  SWModuliQuotient.mk gd sol₁ = SWModuliQuotient.mk gd sol₂ ↔ ∃ g : gd.GaugeGroup, gd.gauge_action g sol₁ = sol₂ :=
-- proof
Quotient.eq (r := gd.gaugeEquivSetoid)

/--
[GaugeActionData.gaugeEquivSetoid_iff_orbitRel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma GaugeActionData.gaugeEquivSetoid_iff_orbitRel
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gd : GaugeActionData spinc}
  {sol₁ sol₂ : SWSolution spinc} :
-- imply
  (gd.gaugeEquivSetoid).r sol₁ sol₂ ↔ (∃ g : gd.GaugeGroup, gd.gauge_action g sol₁ = sol₂) :=
-- proof
  Iff.rfl

/--
[weitzenboeck_maximum_principle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma weitzenboeck_maximum_principle
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [hsc : HasScalarCurvature M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc}
-- given
  (hsc_eq : sol.scalarCurvatureVal = hsc.scalarCurvature) :
-- imply
  hsc.scalarCurvature * sol.supNormSq + sol.supNormSq ^ 2 ≤ 0 := by
-- proof
  have h1 := sol.laplacianTerm_nonneg
  have h2 := sol.covDerivNormSq_nonneg
  have h3 := sol.bochner_eq
  rw [hsc_eq] at h3
  nlinarith [sq_nonneg sol.supNormSq]

/--
[sw_apriori_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
lemma sw_apriori_bound
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [hsc : HasScalarCurvature M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {sol : SWSolution spinc}
-- given
  (hsc_eq : sol.scalarCurvatureVal = hsc.scalarCurvature) :
-- imply
  sol.supNormSq ≤ max (-hsc.scalarCurvature) 0 := by
-- proof
  have hineq := weitzenboeck_maximum_principle sol hsc_eq
  have ht := sol.supNormSq_nonneg
  by_cases ht0 : sol.supNormSq = 0
  · rw [ht0]; exact le_max_right _ _
  · have ht_pos : 0 < sol.supNormSq := lt_of_le_of_ne ht (Ne.symm ht0)
    have h2 : hsc.scalarCurvature + sol.supNormSq ≤ 0 := by
      nlinarith [sq_nonneg sol.supNormSq]
    exact le_max_of_le_left (by linarith)

/--
[posdef_signature_eq_b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
private lemma posdef_signature_eq_b_eq
  {Q : IntersectionForm}
-- given
  (hdef : Q.IsPositiveDefinite) :
-- imply
  Q.signature = (Q.b₂ : ℤ) := by
-- proof
  apply posdef_signature_eq_b Q hdef

/--
[negdef_signature_eq_neg_b](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
private lemma negdef_signature_eq_neg_b_eq
  {Q : IntersectionForm}
-- given
  (hdef : Q.IsNegativeDefinite) :
-- imply
  Q.signature = -((Q.b₂ : ℤ)) := by
-- proof
  apply negdef_signature_eq_neg_b Q hdef

/--
[GaugeEquiv.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
private lemma refl_eq
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [AddCommGroup Ω1]
  [Module ℝ Ω1]
  [AddCommGroup Ω2]
  [Module ℝ Ω2]
  {spinc : SpinCStructure M Ω1 Ω2}
  {gauge : GaugeActionData spinc}
  {sol : SWSolution spinc} :
-- imply
  GaugeEquiv gauge sol sol := by
-- proof
  apply GaugeEquiv.refl gauge sol

/--
[negOneCircle_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean)
-/
@[path]
private lemma negOneCircle_sq_eq :
-- imply
  (negOneCircle : Circle) ^ 2 = 1 := by
-- proof
  apply negOneCircle_sq


-- created on 2026-10-23
