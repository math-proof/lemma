/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Blumenthal01.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Independence.ZeroOne
import Def.v1.Atlas.TheoryOfProbability.code.Blumenthal01
open MeasureTheory MeasurableSpace Filtration


noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- An abstract specification of a *Brownian motion* `B : NNReal → Ω → E`
started at `x ∈ E`, adapted to a filtration `𝓕` on `(Ω, m, μ)`. The fields
require that `μ` is a probability measure, `B 0 = x` almost surely, `B` is
adapted, increments `B_t - B_s` are independent of `𝓕_s` for `s < t`, each
increment has *some* law on `E` (the Gaussian distribution in the standard
case), and the sample paths `t ↦ B_t ω` are continuous for a.e. `ω`. -/
structure IsBrownianMotion {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [TopologicalSpace E] (B : NNReal → Ω → E) (𝓕 : Filtration NNReal m)
    (μ : Measure Ω) (x : E) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  start : ∀ᵐ ω ∂μ, B 0 ω = x
  adapted : Adapted 𝓕 (fun t => B t)
  indep_incr : ∀ s t : NNReal, s < t →
    Indep (𝓕 s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ
  gaussian_incr : ∀ s t : NNReal, s < t →
    ∃ (ν : Measure E), Measure.map (fun ω => B t ω - B s ω) μ = ν
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal => B t ω)

end ProbabilityTheory
end
