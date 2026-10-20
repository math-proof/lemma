import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DiophantineApproximation.ThreeGap
open MetaMathlibExt


/--
[three_gap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/ThreeGap.lean)
-/
@[path]
private lemma three_gap_eq
  {n : ℕ}
  {α : ℝ}
-- given
  (hn : 1 ≤ n)
  (hα : Irrational α) :
-- imply
  ∃ G : Finset ℝ,
    (∀ d : ℝ, d ∈ G ↔ IsThreeGapLength n α d) ∧
    G.card ≤ 3 ∧
    (G.card = 3 → ∃ a b c : ℝ,
    a ∈ G ∧ b ∈ G ∧ c ∈ G ∧ a < b ∧ b < c ∧ c = a + b) := by
-- proof
  apply MetaMathlibExt.three_gap n hn α hα


-- created on 2026-10-20
