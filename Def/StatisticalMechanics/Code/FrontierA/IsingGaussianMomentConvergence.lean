/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianMomentConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianExponentialTightness
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open Filter MeasureTheory Set Topology
open ProbabilityTheory


namespace StatMech.FrontierA

noncomputable def clippedPower (order : Nat) (A : Real) :
    BoundedContinuousFunction Real Real where
  toFun x := max (-|A|) (min (x ^ order) |A|)
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨2 * |A|, ?_⟩
    intro x y
    rw [Real.dist_eq]
    have hbound (z : Real) :
        |max (-|A|) (min (z ^ order) |A|)| <= |A| := by
      rw [abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (neg_le_self (abs_nonneg A)) (min_le_right _ _)
    calc
      |max (-|A|) (min (x ^ order) |A|) -
          max (-|A|) (min (y ^ order) |A|)| <=
          |max (-|A|) (min (x ^ order) |A|)| +
            |max (-|A|) (min (y ^ order) |A|)| := abs_sub _ _
      _ <= |A| + |A| := add_le_add (hbound x) (hbound y)
      _ = 2 * |A| := by ring

end StatMech.FrontierA
