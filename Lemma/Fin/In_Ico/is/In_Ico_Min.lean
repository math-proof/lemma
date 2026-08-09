import sympy.Basic
import sympy.sets.sets
open Int Set Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Fin.In_Ico.is.In_Ico_Min |
| comm | Fin.In_Ico_Min.is.In_Ico |
| mp | Fin.In_Ico_Min.of.In_Ico |
| mpr | Fin.In_Ico.of.In_Ico_Min |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (k : Fin n)
  (a b : ℕ) :
-- imply
  ↑k ∈ Ico a b ↔ ↑k ∈ Ico a (n ⊓ b) := by
-- proof
  grind


-- created on 2026-08-08
