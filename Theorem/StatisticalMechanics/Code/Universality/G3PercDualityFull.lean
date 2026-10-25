/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


theorem dualConfig_eq_comp :
    (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
      = (fun η e => !(η e)) ∘ (Equiv.piCongrLeft (fun _ => Bool) crossEdge) := by
  funext ω e
  simp only [Function.comp_apply, dualConfig]
  rw [Equiv.piCongrLeft_apply]
  simp


theorem measurable_complement :
    Measurable (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) := by
  fun_prop


theorem measurable_reindex :
    Measurable
      (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2))) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crossEdge).measurable


theorem map_complement (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e))
        (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure (1 - p) tsub_le_self := by
  unfold bernoulliProductMeasure
  rw [Measure.infinitePi_map_pi (μ := fun _ : Sym2 (Site 2) => bernoulliMeasure p hp)
      (f := fun _ : Sym2 (Site 2) => (fun b : Bool => !b)) (fun _ => measurable_of_countable _)]
  congr 1
  funext e
  exact bernoulliMeasure_map_not p hp


theorem map_reindex (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (Equiv.piCongrLeft (fun _ => Bool) crossEdge)
        (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure p hp := by
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure p hp) crossEdge


theorem map_dualConfig (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map dualConfig (bernoulliProductMeasure p hp)
      = bernoulliProductMeasure (1 - p) tsub_le_self := by
  rw [dualConfig_eq_comp,
    ← Measure.map_map measurable_complement measurable_reindex,
    map_reindex p hp, map_complement p hp]


end Universality
end StatMech
