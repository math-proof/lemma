import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.Borel

open scoped ContDiff

/--
[borel_jet_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/Borel.lean)
-/
@[path]
private lemma borel_jet_real_eq
-- given
  (a : ℕ → ℝ) :
-- imply
  ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ∀ n : ℕ, iteratedDeriv n f 0 = a n := by
-- proof
  apply Real.Calculus.Borel.borel_jet_real a


-- created on 2026-10-09
