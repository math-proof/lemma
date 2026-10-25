/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SwitchingDichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Def.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


theorem witEnds_not_diag : ∀ i ∈ witM, ¬ (witEnds i).IsDiag := by decide

theorem witM_sources : sources witEnds witM = {0, 1, 2, 3} := by decide

theorem witM_connK_ox : connK witEnds witM 0 1 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩

theorem witM_connK_yg : connK witEnds witM 2 3 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem witM_not_connK_og : ¬ connK witEnds witM 0 3 := by
  
  have hclosed : ∀ a b : Fin 4, adjStep witEnds witM a b → (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) := by
    rintro a b ⟨i, _, ha, hb, _⟩ hab
    fin_cases i
    · 
      simp only [witEnds, Sym2.mem_iff] at ha hb
      rcases hb with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
    · 
      exfalso
      simp only [witEnds, Sym2.mem_iff] at ha
      rcases hab with rfl | rfl <;> rcases ha with h | h <;> exact absurd h (by decide)
  intro h
  
  have hkey : ∀ b : Fin 4, connK witEnds witM 0 b → (b = 0 ∨ b = 1) := by
    intro b hb
    induction hb with
    | refl => exact Or.inl rfl
    | tail _ hstep ih => exact hclosed _ _ hstep ih
  rcases hkey 3 h with h' | h' <;> exact absurd h' (by decide)


theorem disconnect_dichotomy_nonvacuous :
    sources witEnds witM = ({(0 : Fin 4), 1, 2, 3} : Finset (Fin 4))
      ∧ ¬ connK witEnds witM 0 3
      ∧ ((connK witEnds witM 0 1 ∧ connK witEnds witM 2 3)
          ∨ (connK witEnds witM 0 2 ∧ connK witEnds witM 1 3)) :=
  ⟨witM_sources, witM_not_connK_og,
    disconnect_dichotomy witEnds witM witEnds_not_diag
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      witM_sources witM_not_connK_og⟩

end RandomCurrent
end Sharpness
end StatMech
