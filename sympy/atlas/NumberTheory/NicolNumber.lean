/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NicolNumber.lean -/

import Mathlib.Data.Nat.Totient

open scoped BigOperators

namespace MetaMathlibExt

/-- A Nicol number is a positive integer `n` such that
`n ∣ Nat.totient n + σ(n)`.

Concept `jis_term_45b9093105e27ac81a42edd6`; source JIS VOL14/Tang,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Tang2/tang72.tex>, lines 77–90,
SHA-256 `c3e4694f79de76d0563faff13e7ebd325202b73fa5e8fc02045f0fc7b6d3ce0c`. -/
def IsNicolNumber (n : ℕ) : Prop :=
  0 < n ∧ n ∣ Nat.totient n + ∑ d ∈ n.divisors, d

/-- A `t`-Nicol number is a positive integer `n` such that
`Nat.totient n + σ(n) = t * n`. -/
def IsTNicolNumber (t n : ℕ) : Prop :=
  0 < n ∧ Nat.totient n + ∑ d ∈ n.divisors, d = t * n

/-- Every `t`-Nicol number is a Nicol number. -/
theorem IsTNicolNumber.isNicolNumber {t n : ℕ} (h : IsTNicolNumber t n) :
    IsNicolNumber n := by
  refine ⟨h.1, ⟨t, ?_⟩⟩
  simpa [Nat.mul_comm] using h.2

end MetaMathlibExt
