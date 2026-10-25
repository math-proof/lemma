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
import Def.Combinatorics.DixonSummation
/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/


namespace MetaMathlibExt

/-- The extended factorial vanishes at negative integers. -/
@[simp] theorem extFact_of_neg {n : ℤ} (hn : n < 0) : extFact n = 0 := by
  simp [extFact, not_le_of_gt hn]

/-- The extended factorial agrees with `Nat.factorial` on natural inputs. -/
@[simp] theorem extFact_natCast (n : ℕ) : extFact n = n.factorial := by
  simp [extFact]

end MetaMathlibExt
