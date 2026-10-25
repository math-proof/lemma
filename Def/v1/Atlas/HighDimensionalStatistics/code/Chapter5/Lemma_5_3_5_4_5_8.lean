/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
open MeasureTheory InformationTheory


noncomputable section

namespace Chapter5.TVNP

/-- Total variation distance defined as the supremum
`sup_S |P₀(S) - P₁(S)|` over measurable sets. -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ : Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧ x = |(P₀ S).toReal - (P₁ S).toReal|}

/-- Likelihood-ratio test: predict `true` (i.e. `H₁`) iff
`dP₀/dν ≤ dP₁/dν` at `ω`. -/
noncomputable def lrTest {Ω : Type*} [MeasurableSpace Ω]
    (P₁ P₀ ν : Measure Ω) : Ω → Bool :=
  fun ω => decide (P₀.rnDeriv ν ω ≤ P₁.rnDeriv ν ω)

/-- Real-valued KL divergence: `(klDiv P Q).toReal`. -/
noncomputable def klDiv_real {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  (klDiv P Q).toReal

end Chapter5.TVNP
end
