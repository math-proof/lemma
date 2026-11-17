/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Janson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson.Part2
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


public noncomputable section

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
