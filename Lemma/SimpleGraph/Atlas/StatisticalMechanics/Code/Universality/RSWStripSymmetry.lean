import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
open Set SimpleGraph MeasureTheory ProbabilityTheory StatMech StatMech.Universality


/--
[rss_stripReflect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripReflect_zero_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  rss_stripReflect n x 0 = x 0 + 1 := by
-- proof
  apply StatMech.Universality.rss_stripReflect_zero n x

/--
[rss_stripReflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripReflect_one_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  rss_stripReflect n x 1 = 2 * n - 1 - x 1 := by
-- proof
  apply StatMech.Universality.rss_stripReflect_one n x

/--
[rss_stripReflect_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripReflect_symm_zero_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  (rss_stripReflect n).symm x 0 = x 0 - 1 := by
-- proof
  apply StatMech.Universality.rss_stripReflect_symm_zero n x

/--
[rss_stripReflect_symm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripReflect_symm_one_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  (rss_stripReflect n).symm x 1 = 2 * n - 1 - x 1 := by
-- proof
  apply StatMech.Universality.rss_stripReflect_symm_one n x

/--
[rss_adj_stripReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_adj_stripReflect_eq
  {n : ℤ}
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (rss_stripReflect n x) (rss_stripReflect n y) := by
-- proof
  apply StatMech.Universality.rss_adj_stripReflect n x y

/--
[rss_mem_faceStrip_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_mem_faceStrip_reflect_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rss_faceStrip n ↔ rss_stripReflect n x ∈ rss_faceStrip n := by
-- proof
  apply StatMech.Universality.rss_mem_faceStrip_reflect n x

/--
[rss_mem_bottom_reflect_iff_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_mem_bottom_reflect_iff_top_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rss_bottomFaceLine n ↔ rss_stripReflect n x ∈ rss_topFaceLine n := by
-- proof
  apply StatMech.Universality.rss_mem_bottom_reflect_iff_top n x

/--
[rss_mem_top_reflect_iff_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_mem_top_reflect_iff_bottom_eq
  {n : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rss_topFaceLine n ↔ rss_stripReflect n x ∈ rss_bottomFaceLine n := by
-- proof
  apply StatMech.Universality.rss_mem_top_reflect_iff_bottom n x

/--
[rss_dual_reflected_halfWiredBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_dual_reflected_halfWiredBoundary_eq
  {e : rss_StripEnd} :
-- imply
  RSW.dualBC (rss_halfWiredBoundary (rss_reflectEnd e)) = rss_halfWiredBoundary e := by
-- proof
  apply StatMech.Universality.rss_dual_reflected_halfWiredBoundary e

/--
[rss_reflectConfig_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_reflectConfig_apply_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  rss_reflectConfig n omega e = omega (e.map (rss_stripReflect n).symm) := by
-- proof
  apply StatMech.Universality.rss_reflectConfig_apply n omega e

/--
[rss_reflectConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_reflectConfig_measurePreserving_eq
  {n : ℤ} :
-- imply
  MeasurePreserving (rss_reflectConfig n) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
-- proof
  apply StatMech.Universality.rss_reflectConfig_measurePreserving n

/--
[rss_stripDualReflection_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripDualReflection_apply_eq
  {n : ℤ}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  rss_stripDualReflection n omega e = !(omega (fci_faceEdgeEquiv (e.map (rss_stripReflect n).symm))) := by
-- proof
  apply StatMech.Universality.rss_stripDualReflection_apply n omega e

/--
[rss_stripDualReflection_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripDualReflection_measurePreserving_eq
  {n : ℤ} :
-- imply
  MeasurePreserving (rss_stripDualReflection n) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
-- proof
  apply StatMech.Universality.rss_stripDualReflection_measurePreserving n

/--
[rss_stripDualReflection_law](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_stripDualReflection_law_eq
  {n : ℤ} :
-- imply
  Measure.map (rss_stripDualReflection n) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := by
-- proof
  apply StatMech.Universality.rss_stripDualReflection_law n

/--
[rss_strip_symmetry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean)
-/
@[path]
private lemma rss_strip_symmetry_eq
  {n : ℤ} :
-- imply
  (∀ x : Site 2, x ∈ rss_faceStrip n ↔ rss_stripReflect n x ∈ rss_faceStrip n) ∧ (∀ x : Site 2, x ∈ rss_bottomFaceLine n ↔ rss_stripReflect n x ∈ rss_topFaceLine n) ∧ (∀ x : Site 2, x ∈ rss_topFaceLine n ↔ rss_stripReflect n x ∈ rss_bottomFaceLine n) ∧ (∀ e : rss_StripEnd, RSW.dualBC (rss_halfWiredBoundary (rss_reflectEnd e)) = rss_halfWiredBoundary e) ∧ MeasurePreserving (rss_stripDualReflection n) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
-- proof
  apply StatMech.Universality.rss_strip_symmetry n


-- created on 2026-10-23
