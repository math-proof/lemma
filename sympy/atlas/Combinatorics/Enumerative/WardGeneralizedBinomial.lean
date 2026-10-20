/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WardGeneralizedBinomial.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Ring.Nat

open scoped BigOperators

namespace MetaMathlibExt

/-!
# Ward generalized binomial coefficients

Source: T. Edgar and M. Z. Spivey, *Multiplicative Functions, Generalized Binomial
Coefficients, and Generalized Catalan Numbers*, Journal of Integer Sequences 19 (2016),
[`edgar3.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex).
-/

/-- The carry in the units place when adding `n` and `m` in base `b`.
Invalid bases `b ≤ 1` are totalized to zero. -/
def wardUnitsCarry (b n m : ℕ) : ℕ :=
  if 1 < b ∧ b ≤ n % b + m % b then 1 else 0

/-- Ward's product definition of a generalized binomial coefficient:
`{{n+m} choose n}_s = ∏_{b>1} s_b ^ ε₀^{b,n,m}`.

Only bases at most `n + m` can carry in the units place, so this is a finite product.
The source explicitly uses the product as a definition over arbitrary coefficient
sequences, including sequences with zero terms. -/
def wardGeneralizedBinomialCoefficient {R : Type*} [CommMonoid R]
    (s : ℕ → R) (n m : ℕ) : R :=
  ((Finset.range (n + m + 1)).filter fun b => 1 < b).prod
    fun b => s b ^ wardUnitsCarry b n m

/-- `wardUnitsCarry b n m` is the quotient `(n % b + m % b) / b`, for every base `b`. -/
theorem wardUnitsCarry_eq_div (b n m : ℕ) : wardUnitsCarry b n m = (n % b + m % b) / b := by
  unfold wardUnitsCarry
  rcases Nat.lt_or_ge 1 b with hb | hb
  · have hn := Nat.mod_lt n (by omega : 0 < b)
    have hm := Nat.mod_lt m (by omega : 0 < b)
    split_ifs with h
    · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
    · exact (Nat.div_eq_of_lt (by omega)).symm
  · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp [Nat.mod_one]

/-- Ward's generalized binomial coefficient as a product over the bases `2, …, n + m` of
`s b` raised to the units-place carry `(n % b + m % b) / b`. -/
theorem wardGeneralizedBinomialCoefficient_eq_prod_Icc {R : Type*} [CommMonoid R]
    (s : ℕ → R) (n m : ℕ) :
    wardGeneralizedBinomialCoefficient s n m =
      ∏ b ∈ Finset.Icc 2 (n + m), s b ^ ((n % b + m % b) / b) := by
  have hset : (Finset.range (n + m + 1)).filter (fun b => 1 < b) = Finset.Icc 2 (n + m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  simp only [wardGeneralizedBinomialCoefficient, hset, wardUnitsCarry_eq_div]

end MetaMathlibExt
