/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfkforestbuild
import Def.StatisticalMechanics.Code.Walls.btrtrifnotion.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


variable {d : ℕ}


theorem btr_bc60_genuineTrifFinset_empty (L R : ℕ) :
    btr_genuineTrifFinset bc60_upperLines L R = ∅ := by
  classical
  rw [btr_genuineTrifFinset, Finset.filter_eq_empty_iff]
  intro y _
  exact btr_bc60_not_genuineTrif L y


theorem btr_bc60_genuineTcount_zero (L R : ℕ) :
    (btr_genuineTrifFinset bc60_upperLines L R).card = 0 := by
  rw [btr_bc60_genuineTrifFinset_empty]; simp


theorem btr_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2),
      btr_IsGenuineCoarseTrif ω L y → bc61_IsCoarseTrifurcation ω L y) ∧
    
    (∀ (L : ℕ) (y : Site 2), ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y) ∧
    
    (∀ (L R : ℕ), (btr_genuineTrifFinset bc60_upperLines L R).card = 0) :=
  ⟨fun ω L y h => btr_genuine_imp_bc61 h,
   fun L y => btr_bc60_not_genuineTrif L y,
   fun L R => btr_bc60_genuineTcount_zero L R⟩

end StatMech.Walls
