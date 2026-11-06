/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Blumenthal01.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Independence.ZeroOne
open MeasureTheory MeasurableSpace Filtration


noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The *germ σ-algebra at `0`* of a filtration `𝓕` indexed by `NNReal`,
defined as the intersection `⋂_{t > 0} 𝓕_t`. For Brownian motion this is the
`𝓕_0^+` σ-algebra of events observable "immediately after" time `0`; Blumenthal's
0-1 law states that every such event has probability `0` or `1`. -/
@[reducible]
def germSigmaAlgebraZero (𝓕 : Filtration NNReal m) : MeasurableSpace Ω :=
  ⨅ t > (0 : NNReal), 𝓕 t

end ProbabilityTheory
end
