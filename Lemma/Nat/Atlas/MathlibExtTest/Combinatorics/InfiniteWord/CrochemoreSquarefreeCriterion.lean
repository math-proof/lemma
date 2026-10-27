import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion.Part2
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.InfiniteWord MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
open MetaMathlibExt


namespace MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

/--
[shortSquarefreeMorphism_test](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/CrochemoreSquarefreeCriterion.lean)
-/
@[path]
lemma shortSquarefreeMorphism_test
  {w : List TernaryAlphabet}
-- given
  (hlen : w.length ≤ 5)
  (hw : IsSquareFreeWord w) :
-- imply
  IsSquareFreeWord (w.flatMap shortSquarefreeMorphism) := by
-- proof
  obtain _ | ⟨a, w⟩ := w
  · rw [isSquareFreeWord_iff_inits_tails]
    decide
  obtain _ | ⟨b, w⟩ := w
  · fin_cases a <;> rw [isSquareFreeWord_iff_inits_tails] <;> decide
  obtain _ | ⟨c, w⟩ := w
  · fin_cases a <;> fin_cases b <;>
    simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  obtain _ | ⟨d, w⟩ := w
  · fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  obtain _ | ⟨e, w⟩ := w
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  obtain _ | ⟨g, w⟩ := w
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
    simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  · simp at hlen
    omega

end MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion


-- created on 2026-10-23
