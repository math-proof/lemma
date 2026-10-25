/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CallanSequence.lean -/


import Structure.Combinatorics.Enumerative.CallanSequence
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Theorem.MathlibExtTest.Combinatorics.Enumerative.CallanSequence


namespace MetaMathlibExt

def callan11 : CallanSequence 1 1 where
  m := 1
  m_le_n := by decide
  blue := fun i ↦ if i = 0 then {some 0} else {none}
  red := fun i ↦ if i = 0 then {some 0} else {none}
  blue_nonempty := by decide
  red_nonempty := by decide
  blue_covers := by
    intro x
    fin_cases x
    · refine ⟨1, by simp, ?_⟩
      intro y hy
      fin_cases y <;> simp_all
    · refine ⟨0, by simp, ?_⟩
      intro y hy
      fin_cases y <;> simp_all
  red_covers := by
    intro x
    fin_cases x
    · refine ⟨1, by simp, ?_⟩
      intro y hy
      fin_cases y <;> simp_all
    · refine ⟨0, by simp, ?_⟩
      intro y hy
      fin_cases y <;> simp_all
  blue_mem_star := by decide
  red_mem_star := by decide

end MetaMathlibExt
