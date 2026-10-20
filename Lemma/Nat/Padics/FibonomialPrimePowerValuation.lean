import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.FibonomialPrimePowerValuation
open MetaMathlibExt


/--
[padicValNat_fib_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/FibonomialPrimePowerValuation.lean)
-/
@[path]
private lemma padicValNat_fib_mul_eq
  {p : ℕ} [Fact (Nat.Prime p)]
  {m j : ℕ}
-- given
  (hp2 : p ≠ 2)
  (hm : 1 ≤ m)
  (hdvd : p ∣ Nat.fib m)
  (hj : 1 ≤ j) :
-- imply
  padicValNat p (Nat.fib (m * j)) = padicValNat p (Nat.fib m) + padicValNat p j := by
-- proof
  apply MetaMathlibExt.padicValNat_fib_mul p hp2 m hm hdvd j hj

/--
[fibonomial_primePower_padicVal_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/FibonomialPrimePowerValuation.lean)
-/
@[path]
private lemma fibonomial_primePower_padicVal_eq_zero_eq
  {p a b : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (hp5 : p ≠ 5)
  (ha : 0 < a)
  (hab : a ≤ b)
  (hbranch : (p % 5 = 1 ∨ p % 5 = 4) ∨ a % 2 = b % 2) :
-- imply
  padicValNat p
    ((∏ i ∈ Finset.range (p ^ b), Nat.fib (i + 1)) /
    ((∏ i ∈ Finset.range (p ^ a), Nat.fib (i + 1)) *
    ∏ i ∈ Finset.range (p ^ b - p ^ a), Nat.fib (i + 1))) = 0 := by
-- proof
  apply MetaMathlibExt.fibonomial_primePower_padicVal_eq_zero p a b hp hp2 hp5 ha hab hbranch


-- created on 2026-10-20
