import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.L1Quotient

/--
[L1Quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/L1Quotient.lean)
-/
@[path]
private lemma separable_real_banach_quotient_l1_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E] :
-- imply
  ∃ (T : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] E), Function.Surjective T := by
-- proof
  apply FunctionalAnalysis.L1Quotient.separableRealBanach_quotient_l1

-- created on 2026-10-10
