/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RegularVariation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Def.v1.Atlas.TheoryOfProbability.code.DomainAttraction
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal

/-- For a regularly varying function `f` of index `-α` with `α > 0` that is eventually
non-increasing, there exists a sequence `a : ℕ → ℝ` of positive reals (a "generalized
inverse") such that `n · f (a n) → 1` as `n → ∞`. This is a standard tool in the
analysis of domains of attraction for stable laws. -/


namespace ProbabilityTheory

end ProbabilityTheory
noncomputable section

set_option maxHeartbeats 3200000

end
