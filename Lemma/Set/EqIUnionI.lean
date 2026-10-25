import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Fin


/--
[Fin.iUnion_succ_eq_union_last](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {f : Fin (n + 1) → Set α} :
-- imply
  (⋃ i, f i) = (⋃ i : Fin n, f (Fin.castSucc i)) ∪ f (Fin.last n) :=
-- proof
  Fin.iUnion_succ_eq_union_last f


-- created on 2026-10-22
