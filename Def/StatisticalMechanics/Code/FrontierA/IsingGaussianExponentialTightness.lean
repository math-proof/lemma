/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianExponentialTightness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianMomentDeterminacy
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.ContinuousMap.Bounded.Normed
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierA

open ProbabilityTheory


noncomputable def truncatedExpAbs (a : Real) (n : Nat) :
    BoundedContinuousFunction Real Real where
  toFun x := min (Real.exp (a * |x|)) n
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨2 * n, ?_⟩
    intro x y
    rw [Real.dist_eq]
    have hx : 0 <= min (Real.exp (a * |x|)) n :=
      le_min (Real.exp_pos _).le (Nat.cast_nonneg n)
    have hy : 0 <= min (Real.exp (a * |y|)) n :=
      le_min (Real.exp_pos _).le (Nat.cast_nonneg n)
    have hxn : min (Real.exp (a * |x|)) n <= n := min_le_right _ _
    have hyn : min (Real.exp (a * |y|)) n <= n := min_le_right _ _
    rw [abs_le]
    constructor <;> linarith

end StatMech.FrontierA
