import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_1
open RealSimpleFunction


/--
[RealSimpleFunction.disjoint_representation](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → ℝ}
-- given
  (hf: RealSimpleFunction f) :
-- imply
  ∃ (n:ℕ) (v: Fin n → ℝ) (A: Fin n → Set (EuclideanSpace' d)),
        (∀ i, LebesgueMeasurable (A i)) ∧
        Set.univ.PairwiseDisjoint A ∧
        f = ∑ i, (v i) • (A i).indicator' :=
-- proof
  RealSimpleFunction.disjoint_representation hf


-- created on 2026-10-22
