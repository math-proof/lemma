import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.Eq0Add_Pow_3.of.In_Finset_AddSMulS


@[main]
private lemma sub.given
  {x a b c p q δ : ℂ}
  {d : ℤ}
-- given
  (hp : p = b - a ^ 2 / 3)
  (hq : q = a ^ 3 / 27 * 2 + c - a * b / 3)
  (hδ : δ = 4 * p ^ 3 / 27 + q ^ 2)
  (h₀ : ⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q) > π then 1 else -1) = d)
  (h₁ : x = (δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ d + (-δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) - a / 3) :
-- imply
  x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
-- proof
  have h := Complex.Eq0Add_Pow_3.of.In_Finset_AddSMulS.sub.given (x := x + a / 3) hδ h₀ (by rw [h₁]; ring)
  subst hp hq
  linear_combination h


-- created on 2018-11-20
