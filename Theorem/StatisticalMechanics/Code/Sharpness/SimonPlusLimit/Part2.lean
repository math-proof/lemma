/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Def.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


theorem plusMeasure_pair_tendsto (β : ℝ) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0)
      (plusState d β 0)) (x y : Site d) :
    Tendsto
      (fun n ↦ ∫ ω, spin ω x * spin ω y
        ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (plusCorr d β x y)) := by
  simpa only [spinPairBCF_apply, plusCorr] using
    hconv.tendsto_integral (spinPairBCF x y)


end Sharpness
end StatMech
