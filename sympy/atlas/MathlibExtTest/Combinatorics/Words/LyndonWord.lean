/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Words/LyndonWord.lean -/


import sympy.atlas.Combinatorics.Words.LyndonWord
import Lemma.Finset.Words.LyndonWord

import Mathlib.Data.Fin.VecNotation


namespace MathlibExtTest.Combinatorics.Words.LyndonWord

open scoped BigOperators

open MetaMathlibExt

example : wittWordContent (([0, 1] : List (Fin 2)) ++ [0]) = ![2, 1] := by
  rw [wittWordContent_append]
  decide

example : wittWordContent ([1] : List (Fin 2)) = ![0, 1] := by
  rw [wittWordContent_singleton]
  decide

example : wittWordContent (0 :: [0, 1] : List (Fin 2)) = ![2, 1] := by
  rw [wittWordContent_cons]
  decide

example : (∑ i, wittWordContent ([0, 1, 0] : List (Fin 2)) i) = 3 := by
  rw [sum_wittWordContent]
  rfl

example : Fintype.card (WordsOfContent (![2, 1] : Fin 2 → ℕ)) = 3 := by
  rw [card_wordsOfContent_eq_multinomial]
  norm_num [Nat.multinomial, show Nat.factorial 3 / 2 = 3 by decide]

example : IsPrimitiveWord ([0, 0, 1] : List (Fin 2)) := by
  apply isPrimitiveWord_of_isLyndonWord
  constructor
  · simp
  · intro k hk0 hk
    simp at hk
    have hk_cases : k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl <;> decide

example : ([0, 0, 1] : List (Fin 2)).rotate 1 ≠ [0, 0, 1] := by
  apply rotate_ne_of_isPrimitiveWord
  · apply isPrimitiveWord_of_isLyndonWord
    constructor
    · simp
    · intro k hk0 hk
      simp at hk
      have hk_cases : k = 1 ∨ k = 2 := by omega
      rcases hk_cases with rfl | rfl <;> decide
  · decide
  · decide

example : ¬ IsPrimitiveWord ([0, 1, 0, 1] : List (Fin 2)) := by
  rw [isPrimitiveWord_iff_nodup_cyclicPermutations]
  decide

-- There is one Lyndon word with content `(2, 1)`.
example : (Fintype.card (LyndonWordsOfContent (![2, 1] : Fin 2 → ℕ)) : ℚ) = 1 := by
  rw [card_lyndonWordsOfContent_eq_wittMultigradedValue]
  · have hg : Finset.univ.gcd (![2, 1] : Fin 2 → ℕ) = 1 := by decide
    rw [wittMultigradedValue, show ∑ i, (![2, 1] : Fin 2 → ℕ) i = 3 by decide, hg]
    norm_num [Nat.multinomial, show Nat.factorial 3 / 2 = 3 by decide]
  · norm_num

end MathlibExtTest.Combinatorics.Words.LyndonWord
