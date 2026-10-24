/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/HappySixMin.lean -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace MetaMathlibExt.HappySix
/-- Sum of squares of decimal digits. Literal Wanted expression. -/
private def digitSqSum (n : ℕ) : ℕ :=
  (((Nat.digits 10 n).map (fun d => d ^ 2)).sum)

private def IsHap (n : ℕ) : Prop :=
  ∃ k : ℕ, ∃ f : ℕ → ℕ,
    f 0 = n ∧ f k = 1 ∧ ∀ i : ℕ, i < k → f (i + 1) = digitSqSum (f i)

/-- Unhappiness certificate: true if some iterate within fuel hits 0 or 4. -/
private def unhCert : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, n => if n = 0 then true else if n = 4 then true else unhCert k (digitSqSum n)

private def Cmem (c : ℕ) : Prop :=
  c = 0 ∨ c = 4 ∨ c = 16 ∨ c = 37 ∨ c = 58 ∨ c = 89 ∨ c = 145 ∨ c = 42 ∨ c = 20

/-- Happiness certificate: true if some iterate within fuel hits 1. -/
private def hapCert : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, n => if n = 1 then true else hapCert k (digitSqSum n)
end MetaMathlibExt.HappySix
section
namespace MetaMathlibExt
end MetaMathlibExt
end
