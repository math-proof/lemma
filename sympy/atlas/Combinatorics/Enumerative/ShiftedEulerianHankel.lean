/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ShiftedEulerianHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import sympy.atlas.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.StirlingSecondExplicit
import sympy.atlas.NumberTheory.HankelTransform
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

section
namespace MetaMathlibExt

/-- Level-step weights of the Eulerian production matrix. -/
private def euAlpha (x : ℝ) (k : ℕ) : ℝ := (k + 1) * (x + 1)

/-- Down-step weights of the Eulerian production matrix. -/
private def euBeta (x : ℝ) (k : ℕ) : ℝ := k * (k + 1) * x

/-- Closed-form coefficients of the Eulerian moment triangle:
`m ! * C (m + 1) (k + 1) * S (n + 1) (m + 1)`. -/
private def euC (n k m : ℕ) : ℕ :=
  Nat.factorial m * (m + 1).choose (k + 1) * Nat.stirlingSecond (n + 1) (m + 1)

/-- Unnormalized Eulerian triangle rows as polynomials in `x - 1`. -/
private def euS (x : ℝ) (n k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), (euC n k m : ℝ) * (x - 1) ^ (n - m)

/-- Normalized Eulerian moment triangle fed to the weighted-Motzkin lemma. -/
private noncomputable def euM (x : ℝ) (n k : ℕ) : ℝ :=
  euS x n k / (Nat.factorial k : ℝ)

private theorem seh_choose_product_shift : ∀ n : ℕ,
    (∏ j ∈ Finset.range n, ((((j + 2).choose 2 : ℕ) : ℝ)) ^ (n - j)) =
      ∏ k ∈ Finset.range n,
        ((((k + 3).choose 2 : ℕ) : ℝ)) ^ (n - (k + 1))
  | 0 => by simp
  | n + 1 => by
      rw [Finset.prod_range_succ', Finset.prod_range_succ]
      norm_num
end MetaMathlibExt
end
