import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_8_2.Part4
open Chapter7 Chapter7.Series Finset Function Filter
open Chapter8
open Chapter8.Sum


/--
[Sum.of_finite](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_2.lean)
-/
@[path]
private lemma main
  [hX:Finite X]
  {f:X → ℝ} :
-- imply
  Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x :=
-- proof
  Chapter8.Sum.of_finite f


-- created on 2026-10-22
