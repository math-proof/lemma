import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.ArithmeticFunction.SigmaR
open ArithmeticFunction


namespace ArithmeticFunction

/--
[sigmaR_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
lemma sigmaR_apply
  {n : ℕ}
  {s : ℂ} :
-- imply
  sigmaR s n = ∑ d ∈ n.divisors, (d : ℂ) ^ s := by
-- proof
  rfl

end ArithmeticFunction

namespace ArithmeticFunction

/--
[sigmaR_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
lemma sigmaR_apply_one
  {s : ℂ} :
-- imply
  sigmaR s 1 = 1 := by
-- proof
  simp [sigmaR_apply]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[sigmaR_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
lemma sigmaR_zero_apply
  {n : ℕ} :
-- imply
  sigmaR 0 n = (n.divisors.card : ℂ) := by
-- proof
  simp [sigmaR_apply]

end ArithmeticFunction

namespace ArithmeticFunction

/--
[sigmaR_natCast_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/SigmaR.lean)
-/
@[path]
lemma sigmaR_natCast_apply
  {k n : ℕ} :
-- imply
  sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
-- proof
  simp [sigmaR_apply, sigma_apply, Complex.cpow_natCast]

end ArithmeticFunction


-- created on 2026-10-20
-- updated on 2026-10-26
