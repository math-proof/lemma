import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Sequences

/--
[monotone_increasing_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean)
-/
@[path]
lemma monotone_increasing_iff
  {x : ℕ → ℝ} :
-- imply
  Monotone x ↔ ∀ n : ℕ, x n ≤ x (n + 1) := by
-- proof
  constructor
  · intro hm n
    exact hm (Nat.le_succ n)
  · exact monotone_nat_of_le_succ

end Sequences

namespace Sequences

/--
[monotone_decreasing_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Monotone.lean)
-/
@[path]
lemma monotone_decreasing_convergence
  {x : ℕ → ℝ}
-- given
  (hm : Antitone x) :
-- imply
  ((∃ L, Filter.Tendsto x Filter.atTop (nhds L)) ↔ BddBelow (Set.range x)) ∧ (BddBelow (Set.range x) → Filter.Tendsto x Filter.atTop (nhds (⨅ n, x n))) := by
-- proof
  constructor
  · constructor
    · rintro ⟨L, hL⟩
      exact hL.bddBelow_range
    · intro hb
      exact ⟨⨅ n, x n, tendsto_atTop_ciInf hm hb⟩
  · exact tendsto_atTop_ciInf hm

end Sequences


-- created on 2026-10-23
