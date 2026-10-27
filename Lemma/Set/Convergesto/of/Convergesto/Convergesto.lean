import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_9_3.Part2
open Chapter9
open Chapter9.Convergesto


/--
[Convergesto.add](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_3.lean)
-/
@[path]
private lemma main
  {E:Set ℝ}
  {f g: ℝ → ℝ}
  {L M x₀ : ℝ}
-- given
  (hf: Convergesto E f L x₀)
  (hg: Convergesto E g M x₀) :
-- imply
  Convergesto E (f + g) (L + M) x₀ :=
-- proof
  Chapter9.Convergesto.add hf hg


-- created on 2026-10-22
