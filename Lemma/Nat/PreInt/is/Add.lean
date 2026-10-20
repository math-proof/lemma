import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_1
open Section_4_1


/--
[eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_1.lean)
-/
@[path]
private lemma main
  {a b c d:ℕ} :
-- imply
  (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b :=
-- proof
  Section_4_1.PreInt.eq a b c d


-- created on 2026-10-20
