/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StoppingTime.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Stopping
import Def.v1.Atlas.TheoryOfProbability.code.StoppingTime
open MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}


/-- A discrete stopping time with respect to the filtration `f`: a `WithTop ℕ`-valued
function bundled with a proof that it satisfies `IsDiscreteStoppingTime`. -/
structure DiscreteStoppingTime (f : Filtration ℕ m) where
  val : Ω → WithTop ℕ
  property : IsDiscreteStoppingTime f val

