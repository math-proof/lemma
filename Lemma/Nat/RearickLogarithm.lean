import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RearickLogarithm
open MetaMathlibExt


/--
[rearickLog_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RearickLogarithm.lean)
-/
@[path]
private lemma rearickLog_zero_eq
  {f : ArithmeticFunction ℝ}
-- given
  (hf : 0 < f 1) :
-- imply
  rearickLog f hf 0 = 0 := by
-- proof
  apply MetaMathlibExt.rearickLog_zero f hf

/--
[rearickLog_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RearickLogarithm.lean)
-/
@[path]
private lemma rearickLog_one_eq
  {f : ArithmeticFunction ℝ}
-- given
  (hf : 0 < f 1) :
-- imply
  rearickLog f hf 1 = Real.log (f 1) := by
-- proof
  apply MetaMathlibExt.rearickLog_one f hf

/--
[rearickLog_apply_of_one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RearickLogarithm.lean)
-/
@[path]
private lemma rearickLog_apply_of_one_lt_eq
  {f : ArithmeticFunction ℝ}
  {n : ℕ}
-- given
  (hf : 0 < f 1)
  (hn : 1 < n) :
-- imply
  rearickLog f hf n =
    ∑ d ∈ n.divisors,
    f d *
    ArithmeticFunction.dirichletInverse (⇑f)
    (invertibleOfNonzero (ne_of_gt hf)) (n / d) *
    Real.log (d : ℝ) := by
-- proof
  apply MetaMathlibExt.rearickLog_apply_of_one_lt f hf hn

/--
[rearickLog_eq_pmul_log_mul_dirichletInverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RearickLogarithm.lean)
-/
@[path]
private lemma rearickLog_eq_pmul_log_mul_dirichletInverse_eq
  {f : ArithmeticFunction ℝ}
-- given
  (hf : 0 < f 1)
  (h0 : f 1 = 1) :
-- imply
  rearickLog f hf =
    f.pmul ArithmeticFunction.log *
    ArithmeticFunction.dirichletInverse (⇑f) (invertibleOfNonzero (ne_of_gt hf)) := by
-- proof
  apply MetaMathlibExt.rearickLog_eq_pmul_log_mul_dirichletInverse f hf h0

/--
[rearick_log_eq_zero_iff_isMultiplicative](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RearickLogarithm.lean)
-/
@[path]
private lemma rearick_log_eq_zero_iff_isMultiplicative_eq
  {f : ArithmeticFunction ℝ}
-- given
  (hf : 0 < f 1) :
-- imply
  f.IsMultiplicative ↔ ∀ m : ℕ, ¬ IsPrimePow m → rearickLog f hf m = 0 := by
-- proof
  apply MetaMathlibExt.rearick_log_eq_zero_iff_isMultiplicative f hf


-- created on 2026-10-20
