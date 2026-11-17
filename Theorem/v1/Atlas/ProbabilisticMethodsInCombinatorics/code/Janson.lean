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
public import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson.Part2
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology

public section

noncomputable section

namespace JansonInequalities

open Filter Asymptotics Real

/-- For any fixed $k \in \mathbb{N}$, $(n - k) \asymp n$ as $n \to \infty$. -/
lemma isTheta_natCast_sub_const (k : ℕ) :
    (fun n : ℕ => (n : ℝ) - (k : ℝ)) =Θ[atTop] (fun n : ℕ => (n : ℝ)) := by
  constructor
  · apply IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    simp only [one_mul]
    have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)]
    linarith
  · apply IsBigO.of_bound 2
    filter_upwards [Filter.eventually_ge_atTop (2 * k)] with n hn
    have hk : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n from by omega)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith)]
    have : (n : ℝ) / 2 ≤ (n : ℝ) - k := by
      have hcast : (2 * k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    linarith

end JansonInequalities
end
