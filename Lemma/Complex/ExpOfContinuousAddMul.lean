import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.ExpOfContinuousAddMul
open scoped Interval Topology


namespace MetaMathlibExt

/--
[ExpOfContinuousAddMul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExpOfContinuousAddMul.lean)
-/
@[path]
private lemma main
-- given
  (f : ℝ → ℂ)
  (hf : Continuous f)
  (hzero : f 0 = 1)
  (hadd : ∀ r : ℝ, ∀ s : ℝ, f (r + s) = f r * f s) :
-- imply
  ∃ L : ℂ, ∀ r : ℝ, f r = Complex.exp ((r : ℂ) * L) :=
-- proof
  exists_eq_exp_mul_of_continuous_add_mul f hf hzero hadd

end MetaMathlibExt


-- created on 2026-10-11
-- updated on 2026-10-26
