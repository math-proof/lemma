/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_11
open MeasureTheory InformationTheory Real Finset


noncomputable section

namespace MinimaxLowerBound

/-- Minimax probability of a `ϕ`-large squared error:
`inf_{θ̂ measurable} sup_{θ ∈ Θ} P_θ(‖θ̂(Y) - θ‖² ≥ ϕ)`. -/
noncomputable def minimaxRisk {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (Θ : Set (Fin d → ℝ)) (ϕ : ℝ) : ℝ :=
  ⨅ (θhat : { f : Estimator d // Measurable f }),
    ⨆ θ ∈ Θ, (P θ {Y | sqDist (θhat.val Y) θ ≥ ϕ}).toReal

/-- `ℓ⁰` norm of a real vector: the number of non-zero coordinates. -/
def l0norm {d : ℕ} (θ : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => θ i ≠ 0)).card

/-- Sparse parameter set `{θ ∈ ℝ^d : ‖θ‖₀ ≤ k}`. -/
def sparseSet (d : ℕ) (k : ℕ) : Set (Fin d → ℝ) :=
  {θ | l0norm θ ≤ k}

end MinimaxLowerBound
end
