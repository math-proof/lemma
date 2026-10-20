import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.SigmaR
open ArithmeticFunction


/--
[sigmaR_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
private lemma sigmaR_apply_eq
  {n : ℕ}
  {s : ℂ} :
-- imply
  sigmaR s n = ∑ d ∈ n.divisors, (d : ℂ) ^ s := by
-- proof
  apply ArithmeticFunction.sigmaR_apply

/--
[sigmaR_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
private lemma sigmaR_apply_one_eq
  {s : ℂ} :
-- imply
  sigmaR s 1 = 1 := by
-- proof
  apply ArithmeticFunction.sigmaR_apply_one s

/--
[sigmaR_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
private lemma sigmaR_zero_apply_eq
  {n : ℕ} :
-- imply
  sigmaR 0 n = (n.divisors.card : ℂ) := by
-- proof
  apply ArithmeticFunction.sigmaR_zero_apply n

/--
[sigmaR_natCast_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
private lemma sigmaR_natCast_apply_eq
  {k n : ℕ} :
-- imply
  sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
-- proof
  apply ArithmeticFunction.sigmaR_natCast_apply k n


-- created on 2026-10-20
