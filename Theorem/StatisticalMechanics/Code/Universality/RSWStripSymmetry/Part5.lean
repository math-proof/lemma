/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Def.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


theorem rss_stripDualReflection_apply (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rss_stripDualReflection n omega e =
      !(omega (fci_faceEdgeEquiv
        (e.map (rss_stripReflect n).symm))) := by
  rw [rss_stripDualReflection, rss_reflectConfig_apply, fci_faceDualConfig]


theorem rss_stripDualReflection_measurePreserving (n : ℤ) :
    MeasurePreserving (rss_stripDualReflection n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  exact (rss_reflectConfig_measurePreserving n).comp
    fci_faceDualConfig_measurePreserving


theorem rss_stripDualReflection_law (n : ℤ) :
    Measure.map (rss_stripDualReflection n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) =
      bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one :=
  (rss_stripDualReflection_measurePreserving n).map_eq


theorem rss_strip_symmetry (n : ℤ) :
    (∀ x : Site 2,
      x ∈ rss_faceStrip n ↔ rss_stripReflect n x ∈ rss_faceStrip n) ∧
    (∀ x : Site 2,
      x ∈ rss_bottomFaceLine n ↔
        rss_stripReflect n x ∈ rss_topFaceLine n) ∧
    (∀ x : Site 2,
      x ∈ rss_topFaceLine n ↔
        rss_stripReflect n x ∈ rss_bottomFaceLine n) ∧
    (∀ e : rss_StripEnd,
      RSW.dualBC (rss_halfWiredBoundary (rss_reflectEnd e)) =
        rss_halfWiredBoundary e) ∧
    MeasurePreserving (rss_stripDualReflection n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  exact ⟨rss_mem_faceStrip_reflect n,
    rss_mem_bottom_reflect_iff_top n,
    rss_mem_top_reflect_iff_bottom n,
    rss_dual_reflected_halfWiredBoundary,
    rss_stripDualReflection_measurePreserving n⟩

end Universality
end StatMech
