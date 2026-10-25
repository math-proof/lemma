/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.RSW.BoxCrossingUncond.Part3
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace Uncond

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem measureReal_boxCross_ge_halves
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n) :
    μ.real (boxLeftHalf n hn hz0 hzc hzd) * μ.real (boxRightHalf n hn hz0 hzc hzd)
      ≤ μ.real (boxCross n) := by
  have hmb : (n : ℤ) ≤ 2 * n := by linarith
  exact measureReal_horizontalCrossing_ge_halves (a := 0) (m := n) (b := 2 * n) (c := 0)
    (d := n) hn hmb hz0 hzc hzd μ hpa


theorem box_crossing_lower_bound
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hleft : (1 : ℝ) / 2 ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd))
    (hright : (1 : ℝ) / 2 ≤ μ.real (boxRightHalf n hn hz0 hzc hzd)) :
    (1 : ℝ) / 4 ≤ μ.real (boxCross n) := by
  have hprod : (1 : ℝ) / 4
      ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd) * μ.real (boxRightHalf n hn hz0 hzc hzd) := by
    have h1 : (0 : ℝ) ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd) := measureReal_nonneg
    nlinarith [hleft, hright, h1]
  exact le_trans hprod (measureReal_boxCross_ge_halves μ hpa n hn hz0 hzc hzd)


theorem box_crossing_lower_bound_pos
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hleft : (1 : ℝ) / 2 ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd))
    (hright : (1 : ℝ) / 2 ≤ μ.real (boxRightHalf n hn hz0 hzc hzd)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ μ.real (boxCross n) :=
  ⟨1 / 4, by norm_num,
    box_crossing_lower_bound μ hpa n hn hz0 hzc hzd hleft hright⟩

end Uncond
end RSW
end StatMech
