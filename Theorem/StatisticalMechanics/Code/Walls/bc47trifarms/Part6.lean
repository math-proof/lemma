/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
import Def.StatisticalMechanics.Code.Walls.bc47trifarms.Part6
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc47_chainShadow_arms_ok :
    ∀ c : Fin 8, (c = 1 ∨ c = 2) →
      ∃ n₁ n₂ n₃ : Fin 8,
        (bc46_chainLab c n₁ ≠ bc46_chainLab c n₂ ∧ bc46_chainLab c n₁ ≠ bc46_chainLab c n₃ ∧
          bc46_chainLab c n₂ ≠ bc46_chainLab c n₃) ∧
        (∃ z₁, bc46_chainLab c z₁ = bc46_chainLab c n₁ ∧ bc47_chainIsArm z₁ = true) ∧
        (∃ z₂, bc46_chainLab c z₂ = bc46_chainLab c n₂ ∧ bc47_chainIsArm z₂ = true) ∧
        (∃ z₃, bc46_chainLab c z₃ = bc46_chainLab c n₃ ∧ bc47_chainIsArm z₃ = true) := by
  decide


theorem bc47_classical_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x :=
  fun x hxbox htri => absurd htri (hno x hxbox)


theorem bc47_x_mem_box (n : ℕ) : bc47_x ∈ box 2 n := by
  rw [mem_box]; intro i; fin_cases i <;> simp [bc47_x]


theorem bc47_arc_residue_fails_on_fakeConfig (n : ℕ) :
    ¬ arc_TrifArmsRemoveSiteInfinite bc47_fakeConfig n := by
  intro hres
  obtain ⟨c, hadj, hne, ⟨hsep01, _, _⟩, hinf⟩ :=
    hres bc47_x (bc47_x_mem_box n) bc47_isTrifurcation_fakeConfig
  
  have e0 : c 0 = bc47_R 1 := bc47_only_infinite_neighbour_is_R1 (c 0) (hadj 0) (hinf 0)
  have e1 : c 1 = bc47_R 1 := bc47_only_infinite_neighbour_is_R1 (c 1) (hadj 1) (hinf 1)
  
  exact hsep01 (e0.symm ▸ e1.symm ▸ connected_refl _ (bc47_R 1))

end StatMech.Walls
