import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.TripathiPseudoFrobenius
open MetaMathlibExt


/--
[tripathi_pseudo_frobenius_arithmetic_progression_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripathiPseudoFrobenius.lean)
-/
@[path]
private lemma tripathi_pseudo_frobenius_arithmetic_progression_general_eq
  {a d h k q r : ℕ}
  {S : Set ℕ}
-- given
  (ha : 0 < a)
  (hh : 0 < h)
  (hk : 0 < k)
  (hgcd : Nat.gcd a d = 1)
  (hr1 : 1 ≤ r)
  (hrk : r ≤ k)
  (hqr : a - 1 = q * k + r)
  (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧ n = ∑ i ∈ Finset.range (k + 1), c i * (if i = 0 then a else h * a + i * d) }) :
-- imply
  { x | x ∉ S ∧ ∀ s ∈ S, s ≠ 0 → x + s ∈ S } =
    { y | ∃ x : ℕ, a - r ≤ x ∧ x ≤ a - 1 ∧
    y = h * a * ((x - 1) / k) + (h - 1) * a + d * x } := by
-- proof
  apply MetaMathlibExt.tripathi_pseudo_frobenius_arithmetic_progression_general a d h k ha hh hk hgcd q r hr1 hrk hqr S hS

/--
[tripathi_pseudo_frobenius_arithmetic_progression](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripathiPseudoFrobenius.lean)
-/
@[path]
private lemma tripathi_pseudo_frobenius_arithmetic_progression_eq
  {a d h k q r : ℕ}
  {S : Set ℕ}
-- given
  (ha : 0 < a)
  (hd : 0 < d)
  (hh : 0 < h)
  (hk : 0 < k)
  (hgcd : Nat.gcd a d = 1)
  (hr1 : 1 ≤ r)
  (hrk : r ≤ k)
  (hqr : a - 1 = q * k + r)
  (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧ n = ∑ i ∈ Finset.range (k + 1), c i * (if i = 0 then a else h * a + i * d) }) :
-- imply
  { x | x ∉ S ∧ ∀ s ∈ S, s ≠ 0 → x + s ∈ S } =
    { y | ∃ x : ℕ, a - r ≤ x ∧ x ≤ a - 1 ∧
    y = h * a * ((x - 1) / k) + (h - 1) * a + d * x } := by
-- proof
  apply MetaMathlibExt.tripathi_pseudo_frobenius_arithmetic_progression a d h k ha hd hh hk hgcd q r hr1 hrk hqr S hS


-- created on 2026-10-20
