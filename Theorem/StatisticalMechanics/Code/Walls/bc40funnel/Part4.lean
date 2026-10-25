/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc40funnel.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Def.StatisticalMechanics.Code.Walls.bc40funnel.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc40_rootSideComparable_chain_consistent :
    ∃ (rank : Fin 3 → ℕ) (par : Fin 3 → Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop),
      (∀ c u v, R c u v ↔ bc40_chainSiteLab c u = bc40_chainSiteLab c v) ∧
      rank 0 < rank 1 ∧ rank 1 < rank 2 ∧ par 1 = 0 ∧ par 2 = 1 ∧
      (∀ x y : Fin 3, rank x < rank y → x ≠ par y → R y x (par y)) := by
  refine ⟨![0, 1, 2], ![0, 0, 1], (fun c u v => bc40_chainSiteLab c u = bc40_chainSiteLab c v),
    fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · rfl
  · rfl
  · decide

end StatMech.Walls
