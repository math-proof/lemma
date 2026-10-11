
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
Witt's multigraded dimension formula for free Lie algebras.
-/

namespace MetaMathlibExt


/-- Witt's multigraded value `M(n₁, …, nᵣ)`: let `n` be the sum of all entries
of `degree` and `g` their finite gcd; `M` is `(1/n)` times the sum over
positive `d` dividing `g` of `μ(d)` times the multinomial coefficient for
`i ↦ degree i / d` (`ArithmeticFunction.moebius` and `Nat.multinomial`,
coerced into `ℚ`); the `n = 0` boundary is `0`.

Source: Pieter Moree, *Convoluted Convolved Fibonacci Numbers*, Journal of
Integer Sequences 7 (2004), Article 04.2.2, equations `witty`/`basaal`,
lines 598–613 (Möbius inversion of the circular-word count; context
*Circular words and Witt's dimension formula*, lines 574–597),
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Moree/moree12.tex>. -/
def wittMultigradedValue {r : ℕ} (degree : Fin r → ℕ) : ℚ :=
  let n := Finset.sum Finset.univ degree
  let g := Finset.univ.gcd degree
  if n = 0 then 0
  else (1 / (n : ℚ)) * Finset.sum (Nat.divisors g) (fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
      (Nat.multinomial Finset.univ (fun i => degree i / d) : ℚ))


end MetaMathlibExt
