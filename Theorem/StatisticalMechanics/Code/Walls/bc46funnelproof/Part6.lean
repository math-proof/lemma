/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk.Part4
import Def.StatisticalMechanics.Code.Walls.bc46funnelproof.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc46_chainShadow_all_clauses_hold :
    ∀ t s : Fin 8, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨
        (t = 2 ∧ s = 1) ∨ (t = 2 ∧ s = 3) ∨ (t = 3 ∧ s = 2) →
      (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t (bc46_chainB s)) ∧   
      (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t s) ∧                 
      (∀ x : Fin 8, x ≠ t → bc46_chainLab t x = bc46_chainLab t s →           
        bc46_chainLab t (bc46_chainB x) = bc46_chainLab t s) := by
  decide


theorem bc46_chainShadow_guard_nontrivial :
    (bc46_chainLab 2 0 = bc46_chainLab 2 1 ∧ bc46_chainLab 2 5 = bc46_chainLab 2 1) ∧
    (bc46_chainLab 2 3 ≠ bc46_chainLab 2 1 ∧ bc46_chainLab 2 7 ≠ bc46_chainLab 2 1) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end StatMech.Walls
