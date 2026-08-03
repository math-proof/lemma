import Lemma.Nat.Lt_Add_1.of.Le
import Lemma.Set.Ge.of.In_Ico
import Lemma.Set.In_Ico.is.Le.Lt
import Lemma.Set.Le_Sub_1.of.In_Ico
import sympy.functions.elementary.integers
import sympy.sets.sets
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Ico.is.Ge.Le_Sub_1 |
| comm | Set.Ge.Le_Sub_1.is.In_Ico |
| mpr | Set.In_Ico.of.Ge.Le_Sub_1 |
-/
@[main, comm, mpr]
private lemma main
  {x a b : ℤ} :
-- imply
  x ∈ Ico a b ↔ x ≥ a ∧ x ≤ b - 1 := by
-- proof
  constructor
  ·
    intro h
    constructor
    ·
      exact Ge.of.In_Ico h
    ·
      exact Le_Sub_1.of.In_Ico h
  ·
    intro ⟨hGe, hLe⟩
    apply In_Ico.of.Le.Lt
    ·
      exact hGe
    ·
      by_cases h1 : (1 : ℤ) ≤ b
      ·
        exact (Nat.Lt_Add_1.of.Le hLe).trans_eq (IntegerRing.sub_add_cancel h1)
      ·
        have hblt : b - 1 < b := by linarith [not_le.mp h1]
        exact lt_of_le_of_lt hLe hblt


-- created on 2018-05-05
