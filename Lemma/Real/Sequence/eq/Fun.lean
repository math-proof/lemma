import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_1
open Chapter6
open Chapter6.Sequence


/--
[Sequence.inv_coe](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_1.lean)
-/
@[path]
private lemma main
  {a: ℕ → ℝ} :
-- imply
  (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) :=
-- proof
  Chapter6.Sequence.inv_coe a


-- created on 2026-10-22
