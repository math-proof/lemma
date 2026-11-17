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
public import Def.Combinatorics.DixonSummation.Part2

/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/

public section


namespace MetaMathlibExt

/-- The inverse factorial vanishes at negative integers. -/
@[simp] theorem invFact_of_neg {n : ℤ} (hn : n < 0) : invFact n = 0 := by
  simp [invFact, not_le_of_gt hn]

/-- The inverse factorial is the reciprocal of `Nat.factorial` on natural inputs. -/
@[simp] theorem invFact_natCast (n : ℕ) : invFact n = (n.factorial : ℚ)⁻¹ := by
  simp [invFact]

end MetaMathlibExt
