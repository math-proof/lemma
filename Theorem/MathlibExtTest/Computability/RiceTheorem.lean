/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean -/


import Mathlib.Computability.PartrecCode
import Lemma.Nat.RiceTheorem
import Abbrev.MathlibExtTest.Computability.RiceTheorem


-- The standard numbering has a fixed point for the successor index transformer.
example : ∃ e, ∀ n, riceTheoremTest_standardNumbering e n =
    riceTheoremTest_standardNumbering (e + 1) n := by
  exact MetaMathlibExt.acceptableNumbering_fixed_point riceTheoremTest_standardNumbering
    riceTheoremTest_standardNumbering_univ riceTheoremTest_standardNumbering_index
    riceTheoremTest_standardNumbering_smn Computable.succ

-- No computable decider recognizes exactly the programs returning zero at input zero.
example : ¬ ∃ dec : ℕ → ℕ, Nat.Partrec (fun n => Part.some (dec n)) ∧
    ∀ e, (riceTheoremTest_standardNumbering e 0 = Part.some 0 ↔ dec e = 1) ∧
      (riceTheoremTest_standardNumbering e 0 ≠ Part.some 0 ↔ dec e = 0) := by
  apply MetaMathlibExt.rice_theorem riceTheoremTest_standardNumbering
    riceTheoremTest_standardNumbering_row riceTheoremTest_standardNumbering_univ
    riceTheoremTest_standardNumbering_index riceTheoremTest_standardNumbering_smn
    {e | riceTheoremTest_standardNumbering e 0 = Part.some 0}
  · intro a b hab
    change (riceTheoremTest_standardNumbering a 0 = Part.some 0 ↔
      riceTheoremTest_standardNumbering b 0 = Part.some 0)
    rw [hab 0]
  · obtain ⟨a, ha⟩ :=
      riceTheoremTest_standardNumbering_index (fun _ => Part.some 0) Nat.Partrec.zero
    exact ⟨a, ha 0⟩
  · obtain ⟨b, hb⟩ :=
      riceTheoremTest_standardNumbering_index (fun n => Part.some (n + 1)) Nat.Partrec.succ
    refine ⟨b, ?_⟩
    change riceTheoremTest_standardNumbering b 0 ≠ Part.some 0
    rw [hb 0]
    simp

