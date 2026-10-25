/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc50arminjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc48classical.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Def.StatisticalMechanics.Code.Walls.bc50arminjection
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc50_armEndpoint_map_not_injective :
    bc50_shadowArmEnd 0 0 = bc50_shadowArmEnd 1 0 ∧ (0 : Fin 2) ≠ 1 := by
  decide


theorem bc50_abstract_injection_exists :
    ∃ ψ : Fin 2 → Fin 5, Function.Injective ψ ∧ (∀ h, ψ h = 2 ∨ ψ h = 3 ∨ ψ h = 4) := by
  refine ⟨fun h => if h = 0 then 3 else 4, ?_, ?_⟩
  · intro a b hab; fin_cases a <;> fin_cases b <;> simp_all
  · intro h; fin_cases h <;> decide


theorem bc50_injection_notOverStrong (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc48_ClassicalBoundaryArmInjection ω n ↔
        bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n) ∧
      (¬ bc48_ClassicalBoundaryArmInjection ω n ↔
        boxSV_boundaryCard d n < bc48_Tcount_classical d ω n) := by
  refine ⟨bc50_injection_iff_countBound ω n, ?_⟩
  rw [bc50_injection_iff_countBound ω n, not_le]


theorem bc50_clawShadow_distinct_boundary_fires :
    ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) →
      ∃ n₁ n₂ n₃ : Fin 10,
        (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧
          bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧
        (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧
        (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧
        (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) :=
  bc48_clawShadow_classical_fires

end StatMech.Walls
