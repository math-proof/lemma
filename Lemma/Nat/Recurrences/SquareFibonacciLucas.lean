import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.LucasSequence
import Lemma.Nat.LucasSequence


namespace MetaMathlibExt

/--
[lucas_rec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
Source: Refik Keskin and Zafer Yosma, "On Fibonacci and Lucas Numbers of the
Form cx^2", Journal of Integer Sequences 14 (2011), Theorem 2.1, source
lines 129–132,
https://cs.uwaterloo.ca/journals/JIS/VOL14/Keskin/keskin3.tex
complete-source SHA-256
`f0f1dc8d3be32d14f8ad1f44e3c0fcf8c4081345df25ae0e814055b033901ea7`;
raw source-lines 129–132 SHA-256
`c8faa3153ac602a1bfc8d7488b4a14b64315ca1c39ad4ddf97245e574cb203dc`.
The source states: if `Fₙ = x²` then `n = 1, 2, 12`; if `Fₙ = 2x²` then
`n = 3, 6`; if `Lₙ = x²` then `n = 1, 3`; and if `Lₙ = 2x²` then `n = 6`.
The paper attributes the square-Fibonacci classification to J. H. E. Cohn,
"Square Fibonacci numbers, etc.", Fibonacci Quarterly 2.2 (1964), 109–113,
and the Lucas/twice-square classifications to Cohn's related work, including
"Lucas and Fibonacci numbers and some Diophantine equations", Proc. Glasgow
Math. Assoc. 7 (1965), 24–28.
The surrounding paper defines the Fibonacci and Lucas sequences at indices
`0` and `1` and discusses integer indices, but the displayed lists omit the
zero-index exceptions `F₀ = 0` and `L₀ = 2`. Each declaration below therefore
takes `(hn : 0 < n)` to formalize the intended positive-natural-index form.
`Nat.fib` is the Fibonacci sequence and `MetaMathlibExt.lucasNumber` is the
repository's canonical Lucas-number sequence; no parallel `Fₙ₋₁ + Fₙ₊₁`
encoding is used. -/
@[path]
private lemma lucas_rec (m : ℕ) :
  lucasNumber (m + 2) = lucasNumber (m + 1) + lucasNumber m :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cassini](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma cassini (b : ℕ) :
  ((lucasNumber (b + 1) : ℤ)) ^ 2 - (lucasNumber (b + 1) : ℤ) * (lucasNumber b : ℤ)
    - ((lucasNumber b : ℤ)) ^ 2 = 5 * (-1 : ℤ) ^ (b + 1) := by
  induction b with
  | zero => decide
  | succ b ih =>
    have r : lucasNumber (b + 2) = lucasNumber (b + 1) + lucasNumber b := lucas_rec b
    have rZ : ((lucasNumber (b + 2) : ℕ) : ℤ)
      = (lucasNumber (b + 1) : ℤ) + (lucasNumber b : ℤ) := by exact_mod_cast r
    have e1 : b + 1 + 1 = b + 2 := by ring
    rw [e1]
    rw [rZ]
    have hpow : (-1 : ℤ) ^ (b + 2) = -(-1 : ℤ) ^ (b + 1) := by ring
    rw [hpow]
    linear_combination -ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[double_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma double_pair (b : ℕ) :
  ((lucasNumber (2 * b) : ℕ) : ℤ) = ((lucasNumber b : ℕ) : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ b
  ∧ ((lucasNumber (2 * b + 1) : ℕ) : ℤ)
    = ((lucasNumber (b + 1) : ℕ) : ℤ) * ((lucasNumber b : ℕ) : ℤ) - (-1 : ℤ) ^ b := by
  induction b with
  | zero => constructor <;> decide
  | succ b ih =>
    obtain ⟨ihe, iho⟩ := ih
    have hC := cassini b
    have e1 : b + 1 + 1 = b + 2 := by ring
    have hpow : (-1 : ℤ) ^ (b + 1) = -(-1 : ℤ) ^ b := by ring
    have r1 : lucasNumber (2 * (b + 1)) = lucasNumber (2 * b + 1) + lucasNumber (2 * b) := by
      have e : 2 * (b + 1) = (2 * b) + 2 := by ring
      rw [e]; exact lucas_rec (2 * b)
    have r1Z : ((lucasNumber (2 * (b + 1)) : ℕ) : ℤ)
      = ((lucasNumber (2 * b + 1) : ℕ) : ℤ) + ((lucasNumber (2 * b) : ℕ) : ℤ) := by
      exact_mod_cast r1
    have r2 : lucasNumber (2 * (b + 1) + 1)
      = lucasNumber (2 * (b + 1)) + lucasNumber (2 * b + 1) := by
      have e : 2 * (b + 1) + 1 = (2 * b + 1) + 2 := by ring
      have e' : 2 * (b + 1) = (2 * b + 1) + 1 := by ring
      rw [e, e']; exact lucas_rec (2 * b + 1)
    have r2Z : ((lucasNumber (2 * (b + 1) + 1) : ℕ) : ℤ)
      = ((lucasNumber (2 * (b + 1)) : ℕ) : ℤ)
        + ((lucasNumber (2 * b + 1) : ℕ) : ℤ) := by
      exact_mod_cast r2
    have r3 : lucasNumber (b + 1 + 1) = lucasNumber (b + 1) + lucasNumber b := by
      rw [e1]; exact lucas_rec b
    have r3Z : ((lucasNumber (b + 1 + 1) : ℕ) : ℤ)
      = ((lucasNumber (b + 1) : ℕ) : ℤ) + ((lucasNumber b : ℕ) : ℤ) := by
      exact_mod_cast r3
    rw [e1]
    constructor
    · rw [r1Z, ihe, iho, hpow]
      linear_combination -hC
    · rw [r2Z, r1Z, ihe, iho, r3Z, hpow]
      linear_combination -hC

end MetaMathlibExt

namespace MetaMathlibExt

/--
[double_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma double_even (b : ℕ) :
  ((lucasNumber (2 * b) : ℕ) : ℤ) = ((lucasNumber b : ℕ) : ℤ) ^ 2 - 2 * (-1 : ℤ) ^ b :=
  (double_pair b).1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[double_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma double_odd (b : ℕ) :
  ((lucasNumber (2 * b + 1) : ℕ) : ℤ)
    = ((lucasNumber (b + 1) : ℕ) : ℤ) * ((lucasNumber b : ℕ) : ℤ) - (-1 : ℤ) ^ b :=
  (double_pair b).2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[add_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma add_id (a b : ℕ) :
  ((lucasNumber (a + 2 * b) : ℕ) : ℤ)
    = ((lucasNumber (a + b) : ℕ) : ℤ) * ((lucasNumber b : ℕ) : ℤ)
      - (-1 : ℤ) ^ b * ((lucasNumber a : ℕ) : ℤ) := by
  induction a using Nat.twoStepInduction with
  | zero =>
    have e1 : 0 + 2 * b = 2 * b := by ring
    have e2 : 0 + b = b := by ring
    rw [e1, e2]
    have h := double_even b
    have h2 : ((lucasNumber 0 : ℕ) : ℤ) = 2 := rfl
    rw [h2]
    linear_combination h
  | one =>
    have e1 : 1 + 2 * b = 2 * b + 1 := by ring
    have e2 : 1 + b = b + 1 := by ring
    rw [e1, e2]
    have h := double_odd b
    have h1 : ((lucasNumber 1 : ℕ) : ℤ) = 1 := rfl
    rw [h1]
    linear_combination h
  | more a ih1 ih2 =>
    have eL : a + 2 + 2 * b = (a + 2 * b) + 2 := by ring
    have rL : lucasNumber (a + 2 + 2 * b)
      = lucasNumber ((a + 2 * b) + 1) + lucasNumber (a + 2 * b) := by
      rw [eL]; exact lucas_rec (a + 2 * b)
    have rLZ : ((lucasNumber (a + 2 + 2 * b) : ℕ) : ℤ)
      = ((lucasNumber ((a + 2 * b) + 1) : ℕ) : ℤ)
        + ((lucasNumber (a + 2 * b) : ℕ) : ℤ) := by exact_mod_cast rL
    have rN : lucasNumber (a + 2 + b)
      = lucasNumber (a + 1 + b) + lucasNumber (a + b) := by
      have e : a + 2 + b = (a + b) + 2 := by ring
      have e' : a + 1 + b = (a + b) + 1 := by ring
      rw [e, e']; exact lucas_rec (a + b)
    have rNZ : ((lucasNumber (a + 2 + b) : ℕ) : ℤ)
      = ((lucasNumber (a + 1 + b) : ℕ) : ℤ) + ((lucasNumber (a + b) : ℕ) : ℤ) := by
      exact_mod_cast rN
    have rA : lucasNumber (a + 2) = lucasNumber (a + 1) + lucasNumber a := lucas_rec a
    have rAZ : ((lucasNumber (a + 2) : ℕ) : ℤ)
      = ((lucasNumber (a + 1) : ℕ) : ℤ) + ((lucasNumber a : ℕ) : ℤ) := by
      exact_mod_cast rA
    have e3 : (a + 2 * b) + 1 = a + 1 + 2 * b := by ring
    rw [rLZ, e3, ih2, ih1, rNZ, rAZ]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[add_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma add_even (a k : ℕ) (hk : Even k) :
  ((lucasNumber (a + 2 * k) : ℕ) : ℤ)
    = ((lucasNumber (a + k) : ℕ) : ℤ) * ((lucasNumber k : ℕ) : ℤ)
      - ((lucasNumber a : ℕ) : ℤ) := by
  have h := add_id a k
  have hp : (-1 : ℤ) ^ k = 1 := hk.neg_one_pow
  rwa [hp, one_mul] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucas_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma lucas_pos (n : ℕ) : 1 ≤ lucasNumber n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have r := lucas_rec n
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[period_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma period_one (n : ℕ) : lucasNumber (n + 6) % 4 = lucasNumber n % 4 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    have e1 : n + 2 + 6 = (n + 6) + 2 := by ring
    have r1 := lucas_rec (n + 6)
    have r2 := lucas_rec n
    have ih2' : lucasNumber ((n + 6) + 1) % 4 = lucasNumber (n + 1) % 4 := ih2
    rw [e1, r1, r2]
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma period (q r : ℕ) : lucasNumber (6 * q + r) % 4 = lucasNumber r % 4 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : 6 * (q + 1) + r = (6 * q + r) + 6 := by ring
    rwa [e, period_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[v0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma v0 : lucasNumber 0 % 4 = 2 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[v1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma v1 : lucasNumber 1 % 4 = 1 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[v2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma v2 : lucasNumber 2 % 4 = 3 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[v3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma v3 : lucasNumber 3 % 4 = 0 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[v4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma v4 : lucasNumber 4 % 4 = 3 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[v5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma v5 : lucasNumber 5 % 4 = 3 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sq_mod4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma sq_mod4 (x : ℕ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  have h4 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hp : (x ^ 2) % 4 = ((x % 4) ^ 2) % 4 := Nat.pow_mod x 2 4
  obtain h | h | h | h := h4 <;> rw [hp, h] <;> decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[nmod6_of_square](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma nmod6_of_square {n x : ℕ} (h : lucasNumber n = x ^ 2) :
  n % 6 = 1 ∨ n % 6 = 3 := by
  have hn6 : n = 6 * (n / 6) + n % 6 := (Nat.div_add_mod n 6).symm
  have e1 : lucasNumber n % 4 = lucasNumber (n % 6) % 4 := by
    conv_lhs => rw [hn6]
    exact period (n / 6) (n % 6)
  rw [h] at e1
  have hs := sq_mod4 x
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
    have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
    omega
  obtain h0 | h1 | h2 | h3 | h4 | h5 := hr
  · exfalso; rw [h0, v0] at e1; rcases hs with hs | hs <;> rw [hs] at e1 <;>
    exact absurd e1 (by decide)
  · exact Or.inl h1
  · exfalso; rw [h2, v2] at e1; rcases hs with hs | hs <;> rw [hs] at e1 <;>
    exact absurd e1 (by decide)
  · exact Or.inr h3
  · exfalso; rw [h4, v4] at e1; rcases hs with hs | hs <;> rw [hs] at e1 <;>
    exact absurd e1 (by decide)
  · exfalso; rw [h5, v5] at e1; rcases hs with hs | hs <;> rw [hs] at e1 <;>
    exact absurd e1 (by decide)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucas_mod4_of_even_not3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma lucas_mod4_of_even_not3 {k : ℕ} (hk : Even k) (h3 : ¬ 3 ∣ k) :
  lucasNumber k % 4 = 3 := by
  obtain ⟨r, hr⟩ := hk
  have hk6 : k % 6 = 0 ∨ k % 6 = 2 ∨ k % 6 = 4 := by
    have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    omega
  have hk6' : k = 6 * (k / 6) + k % 6 := (Nat.div_add_mod k 6).symm
  have e1 : lucasNumber k % 4 = lucasNumber (k % 6) % 4 := by
    conv_lhs => rw [hk6']
    exact period (k / 6) (k % 6)
  obtain h0 | h2 | h4 := hk6
  · exfalso; apply h3
    have hdvd : 6 ∣ k := Nat.dvd_of_mod_eq_zero h0
    obtain ⟨t, ht⟩ := hdvd
    exact ⟨2 * t, by omega⟩
  · rw [h2, v2] at e1; exact e1
  · rw [h4, v4] at e1; exact e1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[iter_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma iter_dvd (k : ℕ) (hk : Even k) (e j : ℕ) :
  ((lucasNumber k : ℕ) : ℤ) ∣ ((lucasNumber (e + 2 * k * j) : ℕ) : ℤ)
    - (-1 : ℤ) ^ j * ((lucasNumber e : ℕ) : ℤ) := by
  induction j with
  | zero =>
    have e : e + 2 * k * 0 = e := by ring
    rw [e]
    simp
  | succ j ih =>
    have he : e + 2 * k * (j + 1) = (e + 2 * k * j) + 2 * k := by ring
    have hA := add_even (e + 2 * k * j) k hk
    have hp : (-1 : ℤ) ^ (j + 1) = (-1 : ℤ) ^ j * (-1) := by ring
    rw [he, hp, hA]
    have h1 : ((lucasNumber k : ℕ) : ℤ) ∣
      ((lucasNumber ((e + 2 * k * j) + k) : ℕ) : ℤ) * ((lucasNumber k : ℕ) : ℤ) :=
      dvd_mul_left _ _
    have h2 := dvd_sub h1 ih
    have alg : ((((lucasNumber ((e + 2 * k * j) + k) : ℕ) : ℤ)
      * ((lucasNumber k : ℕ) : ℤ) - ((lucasNumber (e + 2 * k * j) : ℕ) : ℤ))
      - (((-1 : ℤ) ^ j * -1) * ((lucasNumber e : ℕ) : ℤ)))
      = ((((lucasNumber ((e + 2 * k * j) + k) : ℕ) : ℤ)
        * ((lucasNumber k : ℕ) : ℤ))
        - ((((lucasNumber (e + 2 * k * j) : ℕ) : ℤ))
          - (-1 : ℤ) ^ j * ((lucasNumber e : ℕ) : ℤ))) := by ring
    rwa [alg]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[three_pow_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma three_pow_odd (r : ℕ) : Odd (3 ^ r) :=
  ((show Odd (3 : ℕ) from by decide)).pow

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobi_neg_one_of_mod4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma jacobi_neg_one_of_mod4 {b : ℕ} (hb : Odd b) (h4 : b % 4 = 3) :
  jacobiSym (-1) b = -1 := by
  rw [jacobiSym.at_neg_one hb, ZMod.χ₄_nat_three_mod_four h4]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[int_gcd_two_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma int_gcd_two_of_odd {b : ℕ} (hb : Odd b) : (2 : ℤ).gcd (b : ℤ) = 1 := by
  obtain ⟨t, ht⟩ := hb
  have hbZ : ((b : ℕ) : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
  have hcop : IsCoprime (2 : ℤ) (((b : ℕ)) : ℤ) := ⟨-(t : ℤ), 1, by linear_combination hbZ⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp hcop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobi_neg_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma jacobi_neg_sq {b : ℕ} {c : ℤ} (hgcd : c.gcd (b : ℤ) = 1)
  (hJ : jacobiSym (-1) b = -1) : jacobiSym (-(c ^ 2)) b = -1 := by
  have hmul : (-(c ^ 2) : ℤ) = (-1) * (c ^ 2) := by ring
  rw [hmul, jacobiSym.mul_left, hJ, jacobiSym.sq_one' hgcd, mul_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobi_sq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma jacobi_sq_nonneg {y : ℤ} {b : ℕ} :
  jacobiSym (y ^ 2) b = 0 ∨ jacobiSym (y ^ 2) b = 1 := by
  have hpow : jacobiSym (y ^ 2) b = jacobiSym y b ^ 2 := jacobiSym.pow_left y 2 b
  obtain h | h | h := jacobiSym.trichotomy y b <;> rw [hpow, h] <;> decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
private lemma key {k e c x n j : ℕ}
  (hkeven : Even k) (hk3 : ¬ 3 ∣ k)
  (he : lucasNumber e = c ^ 2) (hc : c = 1 ∨ c = 2)
  (hj : Odd j) (hn_eq : n = e + 2 * k * j)
  (hsq : lucasNumber n = x ^ 2) : False := by
  have hLk4 : lucasNumber k % 4 = 3 := lucas_mod4_of_even_not3 hkeven hk3
  have hb2 : lucasNumber k % 2 = 1 := by omega
  have hbOdd : Odd (lucasNumber k) := Nat.odd_iff.mpr hb2
  have hJneg1 : jacobiSym (-1) (lucasNumber k) = -1 :=
    jacobi_neg_one_of_mod4 hbOdd hLk4
  have hgcd : ((c : ℕ) : ℤ).gcd ((lucasNumber k : ℕ) : ℤ) = 1 := by
    obtain rfl | rfl := hc
    · simp
    · exact int_gcd_two_of_odd hbOdd
  have hJneg : jacobiSym (-(((c : ℕ) : ℤ) ^ 2)) (lucasNumber k) = -1 :=
    jacobi_neg_sq hgcd hJneg1
  have hdiv := iter_dvd k hkeven e j
  rw [← hn_eq] at hdiv
  have hjneg : (-1 : ℤ) ^ j = -1 := hj.neg_one_pow
  rw [hjneg] at hdiv
  have hsqZ : ((lucasNumber n : ℕ) : ℤ) = ((x : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast hsq
  have heZ : ((lucasNumber e : ℕ) : ℤ) = ((c : ℕ) : ℤ) ^ 2 := by
    exact_mod_cast he
  have hdiv2 : ((lucasNumber k : ℕ) : ℤ)
    ∣ ((x : ℕ) : ℤ) ^ 2 - (-(((c : ℕ) : ℤ) ^ 2)) := by
    have e1 : (-1 : ℤ) * (((c : ℕ) : ℤ) ^ 2) = -((((c : ℕ) : ℤ) ^ 2)) := by ring
    rwa [hsqZ, heZ, e1] at hdiv
  have hsub : ((lucasNumber k : ℕ) : ℤ)
    ∣ (-(((c : ℕ) : ℤ) ^ 2)) - ((x : ℕ) : ℤ) ^ 2 := by
    have e2 : (-(((c : ℕ) : ℤ) ^ 2)) - ((x : ℕ) : ℤ) ^ 2
      = -(((x : ℕ) : ℤ) ^ 2 - (-(((c : ℕ) : ℤ) ^ 2))) := by ring
    rw [e2]
    exact dvd_neg.mpr hdiv2
  have hM : (((x : ℕ) : ℤ) ^ 2)
    ≡ (-(((c : ℕ) : ℤ) ^ 2)) [ZMOD ((lucasNumber k : ℕ) : ℤ)] :=
    (Int.modEq_iff_dvd).mpr hsub
  have hem : ((x : ℕ) : ℤ) ^ 2 % ((lucasNumber k : ℕ) : ℤ)
    = (-(((c : ℕ) : ℤ) ^ 2)) % ((lucasNumber k : ℕ) : ℤ) := hM
  have hJeq : jacobiSym (((x : ℕ) : ℤ) ^ 2) (lucasNumber k)
    = jacobiSym (-(((c : ℕ) : ℤ) ^ 2)) (lucasNumber k) :=
    jacobiSym.mod_left' hem
  rw [hJneg] at hJeq
  have hnn := jacobi_sq_nonneg (y := ((x : ℕ) : ℤ)) (b := lucasNumber k)
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cohn_square_lucas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SquareFibonacciLucas.lean)
-/
@[path]
lemma cohn_square_lucas
  (n x : ℕ)
-- given
  (hn : 0 < n)
  (h : lucasNumber n = x ^ 2) :
-- imply
  n = 1 ∨ n = 3 := by
-- proof
  have hmod6 := nmod6_of_square h
  by_cases h1 : n = 1
  · exact Or.inl h1
  by_cases h3 : n = 3
  · exact Or.inr h3
  have hn5 : 5 ≤ n := by
    obtain hm | hm := hmod6 <;> omega
  have hn2 : n % 2 = 1 := by
    obtain hm | hm := hmod6 <;> omega
  have hn4 : n % 4 = 1 ∨ n % 4 = 3 := (Nat.odd_mod_four_iff).mp hn2
  obtain h41 | h43 := hn4
  · have hL1 : lucasNumber 1 = 1 ^ 2 := by decide
    have h4dvd : 4 ∣ n - 1 := by omega
    obtain ⟨t, ht⟩ := h4dvd
    set m := 2 * t with hm_def
    have hmpos : 0 < m := by omega
    have hmeven : Even m := ⟨t, by omega⟩
    obtain ⟨r, k, hk3, hmk⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hmpos) 3 (by norm_num)
    have hr_odd : Odd (3 ^ r) := three_pow_odd r
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hmk
      omega
    have hkeven : Even k := by
      obtain hk | hk := Nat.even_or_odd k
      · exact hk
      · exfalso
        have hodd_m : Odd m := by rw [hmk]; exact hr_odd.mul hk
        obtain ⟨a, ha⟩ := hmeven
        obtain ⟨b, hb⟩ := hodd_m
        omega
    have h1 : n = 1 + 2 * m := by omega
    have hn_eq : n = 1 + 2 * k * (3 ^ r) := by rw [h1, hmk]; ring
    exact False.elim (key hkeven hk3 hL1 (Or.inl rfl) hr_odd hn_eq h)
  · have hL3 : lucasNumber 3 = 2 ^ 2 := by decide
    have h4dvd : 4 ∣ n - 3 := by omega
    obtain ⟨t, ht⟩ := h4dvd
    set m := 2 * t with hm_def
    have hmpos : 0 < m := by omega
    have hmeven : Even m := ⟨t, by omega⟩
    obtain ⟨r, k, hk3, hmk⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (ne_of_gt hmpos) 3 (by norm_num)
    have hr_odd : Odd (3 ^ r) := three_pow_odd r
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hmk
      omega
    have hkeven : Even k := by
      obtain hk | hk := Nat.even_or_odd k
      · exact hk
      · exfalso
        have hodd_m : Odd m := by rw [hmk]; exact hr_odd.mul hk
        obtain ⟨a, ha⟩ := hmeven
        obtain ⟨b, hb⟩ := hodd_m
        omega
    have h1 : n = 3 + 2 * m := by omega
    have hn_eq : n = 3 + 2 * k * (3 ^ r) := by rw [h1, hmk]; ring
    exact False.elim (key hkeven hk3 hL3 (Or.inr rfl) hr_odd hn_eq h)
end MetaMathlibExt



-- created on 2026-10-20
-- updated on 2026-10-28
