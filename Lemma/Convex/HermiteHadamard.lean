import Mathlib
import sympy.Basic
import sympy.Analysis.Convex.HermiteHadamard

open Convex.HermiteHadamard

/-- [hermite_hadamard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/HermiteHadamard.lean) -/
@[path]
private lemma hermite_hadamard_eq
-- given
  {f : ℝ → ℝ} {a b : ℝ}
  (hab : a < b)
  (hf : ConvexOn ℝ (Set.Icc a b) f) :
-- imply
  f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
-- proof
  apply hermite_hadamard hab hf

-- created on 2026-10-10
