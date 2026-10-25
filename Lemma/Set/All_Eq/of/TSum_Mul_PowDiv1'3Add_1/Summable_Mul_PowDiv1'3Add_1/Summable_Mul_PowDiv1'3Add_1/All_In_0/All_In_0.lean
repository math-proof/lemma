import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[ternary_02_expansion_unique](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d e : ℕ → ℕ}
-- given
  (hd : ∀ j, d j ∈ ({0, 2} : Set ℕ))
  (he : ∀ j, e j ∈ ({0, 2} : Set ℕ))
  (hsum_d : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)))
  (hsum_e : Summable (fun j => (e j : ℝ) * (1/3:ℝ)^(j + 1)))
  (heq : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) = ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1)) :
-- imply
  ∀ j, d j = e j :=
-- proof
  Remark_1_3_10.ternary_02_expansion_unique hd he hsum_d hsum_e heq


-- created on 2026-10-22
