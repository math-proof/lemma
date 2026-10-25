/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc105contraction
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
import Def.StatisticalMechanics.Code.Walls.bc106separated.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc106_separatedTrifFinset_eq_fiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc106_separatedTrifFinset ω L R = bc73_fiber ω L R 0 := by
  classical
  unfold bc106_separatedTrifFinset bc73_fiber
  apply Finset.filter_congr
  intro y hy
  constructor
  · intro hsub; exact bc106_resVec_eq_zero hsub
  · intro hres i
    
    have hposZ : (0 : ℤ) < 2 * L + 1 := by positivity
    have hi : (bc73_resVec L y i).val = (0 : Fin (2 * L + 1)).val := by
      rw [hres]; rfl
    simp only [bc73_resVec, Fin.val_zero] at hi
    have hnn : 0 ≤ y i % (2 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
    have hlt : y i % (2 * L + 1 : ℤ) < 2 * L + 1 := Int.emod_lt_of_pos _ hposZ
    have hmod0 : y i % (2 * L + 1 : ℤ) = 0 := by omega
    exact Int.dvd_of_emod_eq_zero hmod0


theorem bc106_separatedTcount_eq_fiber (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    bc106_separatedTcount ω L R = (bc73_fiber ω L R 0).card := by
  unfold bc106_separatedTcount
  rw [bc106_separatedTrifFinset_eq_fiber]


theorem bc106_separatedTrifFinset_pairwise_disjoint (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    (bc106_separatedTrifFinset ω L R : Set (Site d)).Pairwise
      (fun y y' => Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y')) := by
  rw [bc106_separatedTrifFinset_eq_fiber]
  exact bc73_fiber_pairwise_disjoint ω L R 0


theorem bc106_separated_count_le_boundary_of_forest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc73_SublatticeForest ω L R) :
    bc106_separatedTcount ω L R ≤ boxSV_boundaryCard d R := by
  rw [bc106_separatedTcount_eq_fiber]
  exact h 0


end StatMech.Walls
