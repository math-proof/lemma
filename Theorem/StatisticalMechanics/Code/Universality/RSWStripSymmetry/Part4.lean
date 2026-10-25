/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Def.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part4
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


theorem rss_reflectConfig_apply (n : ℤ)
    (omega : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    rss_reflectConfig n omega e =
      omega (e.map (rss_stripReflect n).symm) := by
  rw [rss_reflectConfig, Equiv.piCongrLeft_apply]
  simp [rss_stripReflectEdge, sym2Congr]


theorem rss_reflectConfig_measurePreserving (n : ℤ) :
    MeasurePreserving (rss_reflectConfig n)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
  refine ⟨(MeasurableEquiv.piCongrLeft
    (fun _ => Bool) (rss_stripReflectEdge n)).measurable, ?_⟩
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) =>
      bernoulliMeasure (2⁻¹ : ℝ≥0) half_le_one)
    (rss_stripReflectEdge n)


end Universality
end StatMech
