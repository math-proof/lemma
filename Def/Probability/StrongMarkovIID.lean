/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovIID.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.Probability.Process.Stopping
public import Structure.v1.Atlas.Probability.code.StoppingTime

@[expose] public section

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
