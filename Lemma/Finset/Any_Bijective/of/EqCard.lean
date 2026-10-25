import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_7_1
open BigOperators
open Classical
open Finset


/--
[exist_bijection](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {X: Finset Y}
-- given
  (hcard: X.card = n) :
-- imply
  ∃ g: Icc (1:ℤ) n → X, Function.Bijective g :=
-- proof
  Finset.exist_bijection X hcard


-- created on 2026-10-20
