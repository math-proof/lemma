import Mathlib
import sympy.Basic
import sympy.functions.special.GaussHypergeometricSummationFrisch


/--
[GaussHypergeometricSummationFrisch](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GaussHypergeometricSummationFrisch.lean)
-/
@[path]
private lemma gauss_hypergeometric_summation_frisch_eq
-- given
  (n : ℕ)
  (b c : ℝ)
  (hn : 1 ≤ n)
  (hcn : (n : ℝ) < c)
  (hb : -1 < b) :
-- imply
  ordinaryHypergeometric (1 + b - c) (n : ℝ) (b + 1) (1 : ℝ) =
    Real.Gamma (c - n) * Real.Gamma (b + 1) /
      (Real.Gamma c * Real.Gamma (b - n + 1)) := by
-- proof
  apply MetaMathlibExt.gauss_hypergeometric_summation_frisch n hn b c hcn hb


-- created on 2026-10-11
