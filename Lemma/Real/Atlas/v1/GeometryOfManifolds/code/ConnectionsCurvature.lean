import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature
open Bundle NormedSpace DifferentialFormSpace
open scoped Manifold ContDiff Topology
open DifferentialFormSpace


/--
[gauge_transformation_curvature](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma gauge_transformation_curvature
  [Ring R]
  {d : R → R}
  {g g_inv A A' dg : R}
-- given
  (hg_left : g_inv * g = 1)
  (_hg_right : g * g_inv = 1)
  (h_gauge : g * A' = A * g + dg)
  (h_d_add : ∀ a b, d (a + b) = d a + d b)
  (h_leib_gA : d (g * A') = dg * A' + g * d A')
  (h_leib_Ag : d (A * g) = d A * g - A * dg)
  (h_dd_g : d dg = 0) :
-- imply
  d A' + A' * A' = g_inv * (d A + A * A) * g := by
-- proof
  have step1 : g * d A' = d A * g - A * dg - dg * A' := by
    have h1 : dg * A' + g * d A' = d A * g - A * dg := by
      have h2 : d (g * A') = d (A * g + dg) := by rw [h_gauge]
      rw [h_leib_gA] at h2
      rwa [h_d_add, h_leib_Ag, h_dd_g, add_zero] at h2
    calc g * d A' = dg * A' + g * d A' - dg * A' := by noncomm_ring
      _ = (d A * g - A * dg) - dg * A' := by rw [h1]
      _ = d A * g - A * dg - dg * A' := by noncomm_ring
  have step2 : g * (d A' + A' * A') = (d A + A * A) * g := by
    calc g * (d A' + A' * A')
      = g * d A' + g * A' * A' := by rw [mul_add, mul_assoc]
      _ = (d A * g - A * dg - dg * A') + (A * g + dg) * A' := by rw [step1, h_gauge]
      _ = d A * g - A * dg + A * (g * A') := by noncomm_ring
      _ = d A * g - A * dg + A * (A * g + dg) := by rw [h_gauge]
      _ = (d A + A * A) * g := by noncomm_ring
  calc d A' + A' * A'
    = g_inv * (g * (d A' + A' * A')) := by
      rw [← mul_assoc, hg_left, one_mul]
    _ = g_inv * ((d A + A * A) * g) := by rw [step2]
    _ = g_inv * (d A + A * A) * g := by rw [mul_assoc]

/--
[totalChernForm_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma totalChernForm_def
  {r : ℕ}
  [CommRing R]
  {curvMatrix : Matrix (Fin r) (Fin r) R}
  {t : R} :
-- imply
  totalChernForm curvMatrix t = (1 + t • curvMatrix).det :=
-- proof
  rfl

/--
[totalChernFormWithScalar_eq_totalChernForm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma totalChernFormWithScalar_eq_totalChernForm
  {r : ℕ}
  [CommRing R]
  [Algebra ℂ R]
  {curvMatrix : Matrix (Fin r) (Fin r) R} :
-- imply
  totalChernFormWithScalar curvMatrix = totalChernForm curvMatrix (algebraMap ℂ R chernScalar) :=
-- proof
  rfl

/--
[totalChernFormWithScalar_rank_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma totalChernFormWithScalar_rank_one
  [CommRing R]
  [Algebra ℂ R]
  {curvMatrix : Matrix (Fin 1) (Fin 1) R} :
-- imply
  totalChernFormWithScalar curvMatrix = 1 + algebraMap ℂ R chernScalar * curvMatrix 0 0 := by
-- proof
  simp only [totalChernFormWithScalar, totalChernForm, Matrix.det_fin_one, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul]

/--
[chernClass_homog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma chernClass_homog
  {r : ℕ}
  [CommRing R]
  [IsGradedFormAlgebra R]
  {curvMatrix : Matrix (Fin r) (Fin r) R}
  {t : R}
  {j : ℕ}
-- given
  (_ht : IsGradedFormAlgebra.IsHomog t 0)
  (_hR : CurvatureMatrixDegreeTwo curvMatrix) :
-- imply
  IsGradedFormAlgebra.IsHomog (chernClass curvMatrix t j) (2 * j) := by
-- proof
  unfold chernClass
  exact IsGradedFormAlgebra.proj_homog (2 * j) _

/--
[chernClassWithScalar_homog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma chernClassWithScalar_homog
  {r : ℕ}
  [CommRing R]
  [Algebra ℂ R]
  [IsGradedFormAlgebra R]
  {curvMatrix : Matrix (Fin r) (Fin r) R}
  {j : ℕ}
-- given
  (ht : ChernScalarHomogZero (R := R))
  (hR : CurvatureMatrixDegreeTwo curvMatrix) :
-- imply
  IsGradedFormAlgebra.IsHomog (chernClassWithScalar curvMatrix j) (2 * j) :=
-- proof
  chernClass_homog curvMatrix _ j ht hR

/--
[firstChernClassRep_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma firstChernClassRep_def
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  {curvature : Ω 2} :
-- imply
  firstChernClassRep (VF := VF) curvature = (1 / (2 * Real.pi)) • curvature :=
-- proof
  rfl

/--
[first_chern_form_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ConnectionsCurvature.lean)
-/
@[path]
lemma first_chern_form_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {curvature : Ω 2}
-- given
  (hcurv : inst.d curvature = 0) :
-- imply
  inst.d (firstChernClassRep (VF := VF) curvature) = 0 := by
-- proof
  simp only [firstChernClassRep_def]
  rw [inst.d_smul, hcurv, smul_zero]


-- created on 2026-10-23
