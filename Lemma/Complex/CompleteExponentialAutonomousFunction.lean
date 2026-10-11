import Mathlib
import sympy.Basic
import sympy.functions.special.CompleteExponentialAutonomousFunction
open MetaMathlibExt


/--
[CompleteExponentialAutonomousFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CompleteExponentialAutonomousFunction.lean)
-/
@[path]
private lemma complete_bell_polynomial_zero_eq
-- given
  (x : ℕ → ℂ) :
-- imply
  completeBellPolynomial 0 x = 1 := by
-- proof
  apply MetaMathlibExt.completeBellPolynomial_zero x

/--
[CompleteExponentialAutonomousFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CompleteExponentialAutonomousFunction.lean)
-/
@[path]
private lemma complete_bell_polynomial_one_eq
-- given
  (x : ℕ → ℂ) :
-- imply
  completeBellPolynomial 1 x = x 0 := by
-- proof
  apply MetaMathlibExt.completeBellPolynomial_one x

/--
[CompleteExponentialAutonomousFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/CompleteExponentialAutonomousFunction.lean)
-/
@[path]
private lemma complete_bell_polynomial_two_eq
-- given
  (x : ℕ → ℂ) :
-- imply
  completeBellPolynomial 2 x = x 0 ^ 2 + x 1 := by
-- proof
  apply MetaMathlibExt.completeBellPolynomial_two x


-- created on 2026-10-11
