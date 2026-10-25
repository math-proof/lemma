/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ShiftedEulerianHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Def.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
import Lemma.Finset.Enumerative.StirlingSecondExplicit
import Def.NumberTheory.HankelTransform
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

/-- Level-step weights of the Eulerian production matrix. -/
def euAlpha (x : ℝ) (k : ℕ) : ℝ := (k + 1) * (x + 1)

/-- Down-step weights of the Eulerian production matrix. -/
def euBeta (x : ℝ) (k : ℕ) : ℝ := k * (k + 1) * x

/-- Closed-form coefficients of the Eulerian moment triangle:
`m ! * C (m + 1) (k + 1) * S (n + 1) (m + 1)`. -/
def euC (n k m : ℕ) : ℕ :=
  Nat.factorial m * (m + 1).choose (k + 1) * Nat.stirlingSecond (n + 1) (m + 1)

/-- Unnormalized Eulerian triangle rows as polynomials in `x - 1`. -/
def euS (x : ℝ) (n k : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), (euC n k m : ℝ) * (x - 1) ^ (n - m)

/-- Normalized Eulerian moment triangle fed to the weighted-Motzkin lemma. -/
noncomputable def euM (x : ℝ) (n k : ℕ) : ℝ :=
  euS x n k / (Nat.factorial k : ℝ)

end MetaMathlibExt
end
