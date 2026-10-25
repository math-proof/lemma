/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson.Part2
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


noncomputable section

namespace JansonInequalities

open Filter Asymptotics Real

/-- Bundle of asymptotic data for triangles in $G(n, p(n))$: triangle-free probability,
Janson parameters $\mu$ and $\Delta$ with their correct asymptotic order. -/
structure TriangleFreeGnpData (p : ℕ → ℝ) where
  prob_tf : ℕ → ℝ
  μ : ℕ → ℝ
  Δ : ℕ → ℝ
  prob_tf_pos : ∀ᶠ n in atTop, 0 < prob_tf n
  prob_tf_le_one : ∀ᶠ n in atTop, prob_tf n ≤ 1
  μ_isTheta : μ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3)
  Δ_isTheta : Δ =Θ[atTop] (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5)
  Δ_pos : ∀ᶠ n in atTop, 0 < Δ n

end JansonInequalities
end
