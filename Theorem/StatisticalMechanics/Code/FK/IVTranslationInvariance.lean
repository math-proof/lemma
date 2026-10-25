/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IVTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull.Part2
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


theorem ivt_integral_wiredShifted {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    (∫ x, f x ∂((erg_wiredShiftedFinite hp hp1 hq g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((wiredFiniteMeasure d n hp hp1 hq : ProbabilityMeasure _) : Measure _) := by
  unfold erg_wiredShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]


theorem ivt_integral_freeShifted {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (g : Multiplicative (Site d)) (n : ℕ) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    (∫ x, f x ∂((erg_freeShiftedFinite hp hp1 hq g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((freeFiniteMeasure d n hp hp1 hq : ProbabilityMeasure _) : Measure _) := by
  unfold erg_freeShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]


end FK
end StatMech
