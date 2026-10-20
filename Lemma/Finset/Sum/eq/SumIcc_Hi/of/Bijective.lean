import Mathlib
import sympy.Basic
import sympy.analysis.Section_7_1
open Finset


/--
[finite_series_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {X: Finset Y}
  {f: Y → ℝ}
  {g: Icc (1:ℤ) n → X}
-- given
  (hg: Function.Bijective g) :
-- imply
  ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) :=
-- proof
  Finset.finite_series_eq X f g hg


-- created on 2026-10-20
