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
import Def.Combinatorics.Enumerative.ShiftedEulerianHankel


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
