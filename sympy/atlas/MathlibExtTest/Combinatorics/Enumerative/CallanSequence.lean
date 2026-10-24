/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CallanSequence.lean -/


import sympy.atlas.Combinatorics.Enumerative.CallanSequence
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt

private def callan00 : CallanSequence 0 0 where
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

example : callan00.m = 0 := rfl

example : callan00.m ≤ 0 := callan00.m_le_n

example : (none : Option (Fin 0)) ∈ callan00.blue (Fin.last callan00.m) :=
  callan00.blue_mem_star

example : (none : Option (Fin 0)) ∈ callan00.red (Fin.last callan00.m) :=
  callan00.red_mem_star

example (x : Option (Fin 0)) : ∃! i, x ∈ callan00.blue i :=
  callan00.blue_covers x

example (x : Option (Fin 0)) : ∃! i, x ∈ callan00.red i :=
  callan00.red_covers x

private def callan11 : CallanSequence 1 1 where
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

example : (some 0 : Option (Fin 1)) ∈ callan11.blue 0 := by decide

example : (some 0 : Option (Fin 1)) ∈ callan11.red 0 := by decide

example : (none : Option (Fin 1)) ∈ callan11.blue (Fin.last callan11.m) :=
  callan11.blue_mem_star

example : (none : Option (Fin 1)) ∈ callan11.red (Fin.last callan11.m) :=
  callan11.red_mem_star

example (x : Option (Fin 1)) : ∃! i, x ∈ callan11.blue i :=
  callan11.blue_covers x

example (x : Option (Fin 1)) : ∃! i, x ∈ callan11.red i :=
  callan11.red_covers x

end MetaMathlibExt
