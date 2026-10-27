import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch7PowerDifference

open Ramanujan.Part1Ch7


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

/--
[Part1Ch7PowerDifference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean)
-/
@[path]
lemma chapter7Admissible_zero
-- imply
  chapter7Admissible 0 := by
-- proof
  intro j
  rw [add_zero]
  exact_mod_cast Nat.succ_ne_zero j

end MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

/--
[Part1Ch7PowerDifference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean)
-/
@[path]
lemma chapter7PowerDifferenceTerm_zero_left
-- given
  (x : ℂ)
  (j : ℕ) :
-- imply
  chapter7PowerDifferenceTerm 0 x j = 0 := by
-- proof
  simp [chapter7PowerDifferenceTerm]

end MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

/--
[Part1Ch7PowerDifference](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7PowerDifference.lean)
-/
@[path]
lemma chapter7PowerDifferenceTerm_zero_right
-- given
  (r : ℂ)
  (j : ℕ) :
-- imply
  chapter7PowerDifferenceTerm r 0 j = 0 := by
-- proof
  simp [chapter7PowerDifferenceTerm]
end



-- created on 2026-10-10
-- updated on 2026-10-26
