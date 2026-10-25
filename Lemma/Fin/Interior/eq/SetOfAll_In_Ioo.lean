import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open DyadicCube


/--
[interior](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {n:ℤ}
  {a: Fin d → ℤ} :
-- imply
  interior (DyadicCube n a).toSet =
    {x | ∀ i, x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n)} :=
-- proof
  DyadicCube.interior n a


-- created on 2026-10-22
