/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ShiftedEulerianHankel.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Def.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant
public import Theorem.Finset.Enumerative.HeilermannWeightedMotzkinDeterminant
public import Theorem.Finset.Enumerative.StirlingSecondExplicit
public import Def.NumberTheory.HankelTransform
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.ShiftedEulerianHankel

public section

section

namespace MetaMathlibExt

theorem seh_choose_product_shift : ∀ n : ℕ,
    (∏ j ∈ Finset.range n, ((((j + 2).choose 2 : ℕ) : ℝ)) ^ (n - j)) =
      ∏ k ∈ Finset.range n,
        ((((k + 3).choose 2 : ℕ) : ℝ)) ^ (n - (k + 1))
  | 0 => by simp
  | n + 1 => by
      rw [Finset.prod_range_succ', Finset.prod_range_succ]
      norm_num

end MetaMathlibExt
end
