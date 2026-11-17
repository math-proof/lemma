/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonSummation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.DixonSummation

@[expose] public section

/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/


namespace MetaMathlibExt

/-- Inverse factorial: reciprocal factorial for `n >= 0`, zero for `n < 0`. -/
def invFact (n : ℤ) : ℚ :=
  if 0 ≤ n then 1 / (n.natAbs.factorial : ℚ) else 0

end MetaMathlibExt
