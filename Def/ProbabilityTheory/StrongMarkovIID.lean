/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovIID.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Process.Stopping
import Structure.v1.Atlas.TheoryOfProbability.code.StoppingTime
open MeasureTheory ProbabilityTheory


noncomputable section

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

variable {S : Type*} [MeasurableSpace S]

/-- The **post-stopping-time sequence** `(X_{T+k+1})_{k ≥ 0}` obtained from a sequence
`X : ℕ → Ω → S` by shifting the index by `T(ω) + 1`. This is the sequence of observations
immediately after the stopping time `T`. -/
def postStoppingTimeSeq (X : ℕ → Ω → S) (T : Ω → ℕ) : ℕ → Ω → S :=
  fun k ω => X (T ω + k + 1) ω

end
