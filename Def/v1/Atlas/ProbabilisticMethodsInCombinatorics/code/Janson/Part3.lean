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
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Janson
set_option maxHeartbeats 800000

open Filter Real
open scoped Topology


noncomputable section

namespace JansonInequalities

open Filter Asymptotics Real

/-- Constructs a `TriangleFreeGnpData` bundle for a probability sequence $p(n)$ that is
eventually positive and bounded away from $1$. The triangle-free probability used is the
naive empty-graph bound $(1-p)^{\binom{n}{2}}$ for the lower bound. -/
def triangleFreeGnpData_exists (p : ℕ → ℝ)
    (hp_pos : ∀ᶠ n in atTop, 0 < p n)
    (hp_le : ∀ᶠ n in atTop, p n ≤ 0.99) :
    TriangleFreeGnpData p := by
  refine ⟨fun n => (1 - p n) ^ Nat.choose n 2,
         fun n => Janson.mu_triangles n (p n),
         fun n => Janson.delta_triangles n (p n), ?_, ?_, ?_, ?_, ?_⟩
  ·
    filter_upwards [hp_pos, hp_le] with n hp hle
    apply pow_pos; linarith
  ·
    filter_upwards [hp_pos, hp_le] with n hp hle
    apply pow_le_one₀ (by linarith) (by linarith)
  ·
    show (fun n : ℕ => (n.choose 3 : ℝ) * p n ^ 3) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 3 * p n ^ 3)
    exact (isTheta_choose 3).mul (isTheta_refl _ _)
  ·
    show (fun n : ℕ => (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3) * p n ^ 5) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 4 * p n ^ 5)
    have h_coeff : (fun n : ℕ => (n.choose 2 : ℝ) * ((n : ℝ) - 2) * ((n : ℝ) - 3)) =Θ[atTop]
        (fun n : ℕ => (n : ℝ) ^ 4) := by
      have h1 := isTheta_choose 2
      have h2 := isTheta_natCast_sub_const 2
      have h3 := isTheta_natCast_sub_const 3
      have hmul := h1.mul h2 |>.mul h3
      have heq : (fun n : ℕ => (n : ℝ) ^ 2 * (↑n) * (↑n)) = (fun n : ℕ => (n : ℝ) ^ 4) := by
        ext n; ring
      rwa [heq] at hmul
    exact h_coeff.mul (isTheta_refl _ _)
  ·
    filter_upwards [hp_pos, Filter.eventually_ge_atTop 4] with n hp hn
    simp only [Janson.delta_triangles]
    have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by
      have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hcn2 : (0 : ℝ) < (n.choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : 2 ≤ n)
    apply mul_pos
    · apply mul_pos
      · exact mul_pos hcn2 hn2
      · exact hn3
    · positivity

end JansonInequalities
end
