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
import Theorem.Combinatorics.DixonSummation.Part4
/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/


namespace MetaMathlibExt

def dixon_kernel (a b c k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * invFact (a + k) * invFact (a - k) *
    invFact (b + k) * invFact (b - k) * invFact (c + k) * invFact (c - k)

def dixon_phi (a b c : ℤ) : ℚ :=
  extFact (a + b + c) * invFact (a + b) * invFact (a + c) *
    invFact (b + c) * invFact a * invFact b * invFact c

def dixon_certificate (a b c k : ℤ) : ℚ :=
  -((-1 : ℚ) ^ k) / (2 * (a + b + c + 1)) *
    invFact (a + k - 1) * invFact (a - k) *
    invFact (b + k - 1) * invFact (b - k) *
    invFact (c + k) * invFact (c + 1 - k) / dixon_phi a b c

end MetaMathlibExt
