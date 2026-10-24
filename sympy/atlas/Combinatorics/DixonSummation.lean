/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/

namespace MetaMathlibExt

/-- Extended factorial: ordinary factorial for `n >= 0`, zero for `n < 0`. -/
def extFact (n : ℤ) : ℚ :=
  if 0 ≤ n then (n.natAbs.factorial : ℚ) else 0

/-- The extended factorial vanishes at negative integers. -/
@[simp] theorem extFact_of_neg {n : ℤ} (hn : n < 0) : extFact n = 0 := by
  simp [extFact, not_le_of_gt hn]

/-- The extended factorial agrees with `Nat.factorial` on natural inputs. -/
@[simp] theorem extFact_natCast (n : ℕ) : extFact n = n.factorial := by
  simp [extFact]

/-- Inverse factorial: reciprocal factorial for `n >= 0`, zero for `n < 0`. -/
def invFact (n : ℤ) : ℚ :=
  if 0 ≤ n then 1 / (n.natAbs.factorial : ℚ) else 0

/-- The inverse factorial vanishes at negative integers. -/
@[simp] theorem invFact_of_neg {n : ℤ} (hn : n < 0) : invFact n = 0 := by
  simp [invFact, not_le_of_gt hn]

/-- The inverse factorial is the reciprocal of `Nat.factorial` on natural inputs. -/
@[simp] theorem invFact_natCast (n : ℕ) : invFact n = (n.factorial : ℚ)⁻¹ := by
  simp [invFact]

/-- Integer binomial coefficient with the source zero conventions. -/
def intBinom (n k : ℤ) : ℚ :=
  extFact n * invFact k * invFact (n - k)

/-- Integer binomial coefficients agree with `Nat.choose` on their natural range. -/
@[simp] theorem intBinom_natCast {n k : ℕ} (hk : k ≤ n) :
    intBinom n k = n.choose k := by
  rw [intBinom, ← Int.ofNat_sub hk]
  simp only [extFact_natCast, invFact_natCast]
  rw [Nat.cast_choose ℚ hk]
  field_simp

/-- Integer binomial coefficients vanish when the lower argument is negative. -/
@[simp] theorem intBinom_of_neg_right {n k : ℤ} (hk : k < 0) : intBinom n k = 0 := by
  simp [intBinom, invFact_of_neg hk]

/-- Integer binomial coefficients vanish when the upper argument is below the lower one. -/
@[simp] theorem intBinom_of_lt {n k : ℤ} (h : n < k) : intBinom n k = 0 := by
  simp [intBinom, invFact_of_neg (show n - k < 0 by omega)]

/-- Single summand of `upsilon_3`: `(-1)^k` times the three binomial factors. -/
def dixonSummand (a₁ a₂ a₃ k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k.natAbs * intBinom (2 * a₁) (a₁ + k) *
    (intBinom (2 * a₂) (a₂ + k) * intBinom (2 * a₃) (a₃ + k))

/-- Faithful finite-support bound: every nonzero summand satisfies `|k| ≤ bound`. -/
def dixonBound (a₁ a₂ a₃ : ℤ) : ℤ :=
  max (|a₁|) (max (|a₂|) (|a₃|))

/-- `upsilon_3`: finite-support alternating sum over all integers `k`. -/
def upsilon₃ (a₁ a₂ a₃ : ℤ) : ℚ :=
  ∑ k ∈ Finset.Icc (-(dixonBound a₁ a₂ a₃)) (dixonBound a₁ a₂ a₃),
    dixonSummand a₁ a₂ a₃ k

example : extFact (-3 : ℤ) = 0 := by
  simp [extFact]

example : extFact (0 : ℤ) = 1 := by
  simp [extFact]

example : extFact (5 : ℤ) = 120 := by
  have hle : (0 : ℤ) ≤ 5 := by decide
  have habs : (5 : ℤ).natAbs = 5 := rfl
  have hfac : Nat.factorial 5 = 120 := by decide
  simp [extFact, hle, habs, hfac]

example : invFact (-2 : ℤ) = 0 := by
  simp [invFact]

example : invFact (0 : ℤ) = 1 := by
  simp [invFact]

example : invFact (3 : ℤ) = 1 / 6 := by
  have hle : (0 : ℤ) ≤ 3 := by decide
  have habs : (3 : ℤ).natAbs = 3 := rfl
  have hfac : Nat.factorial 3 = 6 := by decide
  simp [invFact, hle, habs, hfac]

example : intBinom (4 : ℤ) (2 : ℤ) = 6 := by
  have h4 : extFact (4 : ℤ) = 24 := by
    have hle : (0 : ℤ) ≤ 4 := by decide
    have habs : (4 : ℤ).natAbs = 4 := rfl
    have hfac : Nat.factorial 4 = 24 := by decide
    simp [extFact, hle, habs, hfac]
  have h2 : invFact (2 : ℤ) = 1 / 2 := by
    have hle : (0 : ℤ) ≤ 2 := by decide
    have habs : (2 : ℤ).natAbs = 2 := rfl
    have hfac : Nat.factorial 2 = 2 := by decide
    simp [invFact, hle, habs, hfac]
  simp [intBinom, h4, h2]
  norm_num

example : upsilon₃ (0 : ℤ) 0 0 = 1 := by
  have hbound : dixonBound (0 : ℤ) 0 0 = 0 := by decide
  have h0 : extFact (0 : ℤ) = 1 := by simp [extFact]
  have hi0 : invFact (0 : ℤ) = 1 := by simp [invFact]
  simp [upsilon₃, hbound, dixonSummand, intBinom, h0, hi0]

private def dixon_kernel (a b c k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
    invFact (b + k) * invFact (b - k) * invFact (c + k) * invFact (c - k)

private def dixon_phi (a b c : ℤ) : ℚ :=
  extFact (a + b + c) * invFact (a + b) * invFact (a + c) *
    invFact (b + c) * invFact a * invFact b * invFact c

private def dixon_certificate (a b c k : ℤ) : ℚ :=
  -((-1 : ℚ) ^ k) / (2 * (a + b + c + 1)) *
    invFact (a + k - 1) * invFact (a - k) *
    invFact (b + k - 1) * invFact (b - k) *
    invFact (c + k) * invFact (c + 1 - k) / dixon_phi a b c
end MetaMathlibExt
