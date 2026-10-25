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
import Def.Combinatorics.DixonSummation.Part4
/-!
Source: Abdelmalek Abdesselam, "An algebraic independence result related to a
conjecture of Dixmier on binary form invariants", arXiv:1903.11147v2,
published in Research in the Mathematical Sciences 6 (2019), article 26.
Factorial conventions: TeX lines 322-349; upsilon_m definition: lines 415-421;
Proposition (Dixon), terminating 3F2 summation: lines 502-512.
-/


namespace MetaMathlibExt

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

end MetaMathlibExt
