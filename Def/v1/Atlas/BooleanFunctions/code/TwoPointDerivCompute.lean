/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/TwoPointDerivCompute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

open Real Set


namespace BooleanFourier

section LogPathDerivative

set_option maxHeartbeats 800000

noncomputable def twoPointLogPathFn (p : ℝ) (a b : ℝ) (t : ℝ) : ℝ :=
  let r := 1 + (p - 1) / t ^ 2
  let c := (1 + t) / 2 * a + (1 - t) / 2 * b
  let d := (1 - t) / 2 * a + (1 + t) / 2 * b
  (1 / r) * Real.log ((c ^ r + d ^ r) / 2)

noncomputable def twoPointLogPathFn_derivValue (p a b t : ℝ) : ℝ :=
  let r := 1 + (p - 1) / t ^ 2
  let c := (1 + t) / 2 * a + (1 - t) / 2 * b
  let d := (1 - t) / 2 * a + (1 + t) / 2 * b
  let S := c ^ r + d ^ r
  let r' := -2 * (p - 1) / t ^ 3
  let c' := (a - b) / 2
  let d' := (b - a) / 2

  let S' := c' * r * c ^ (r - 1) + r' * c ^ r * Real.log c +
            d' * r * d ^ (r - 1) + r' * d ^ r * Real.log d

  (-r' / r ^ 2) * Real.log (S / 2) + (1 / r) * (S' / S)

noncomputable def twoPointLogSumGap (p a b t : ℝ) : ℝ :=
  let r := 1 + (p - 1) / t ^ 2
  let c := (1 + t) / 2 * a + (1 - t) / 2 * b
  let d := (1 - t) / 2 * a + (1 + t) / 2 * b
  let S := c ^ r + d ^ r
  (c ^ r * Real.log c + d ^ r * Real.log d) / S - (1 / r) * Real.log (S / 2)

end LogPathDerivative
end BooleanFourier
