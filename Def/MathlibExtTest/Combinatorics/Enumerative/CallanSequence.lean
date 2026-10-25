/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CallanSequence.lean -/


import Structure.Combinatorics.Enumerative.CallanSequence
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases


namespace MetaMathlibExt

def callan00 : CallanSequence 0 0 where
  m := 0
  m_le_n := by decide
  blue := fun _ ↦ {none}
  red := fun _ ↦ {none}
  blue_nonempty := by
    intro i
    exact ⟨none, by simp⟩
  red_nonempty := by
    intro i
    exact ⟨none, by simp⟩
  blue_covers := by
    intro x
    refine ⟨0, ?_, ?_⟩
    · cases x with
      | none => simp
      | some x => exact Fin.elim0 x
    intro y hy
    exact Fin.eq_zero y
  red_covers := by
    intro x
    refine ⟨0, ?_, ?_⟩
    · cases x with
      | none => simp
      | some x => exact Fin.elim0 x
    intro y hy
    exact Fin.eq_zero y
  blue_mem_star := by simp
  red_mem_star := by simp

end MetaMathlibExt
