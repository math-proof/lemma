/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc55route
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Def.StatisticalMechanics.Code.Walls.bc56menger
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc56_clusterAttachment_of_reachesNbr (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc56_ClusterReachesNbr ω x) : bma_ClusterAttachment ω x := by
  classical
  obtain ⟨a, hadj, hmem, hreach, hinf⟩ := h
  have hforce : forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
    funext e; simp [forceOpenFinset]
  refine ⟨a, ∅, hadj, ?_, ?_, hmem, ?_, hinf⟩
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · intro e he; exact absurd he (Finset.notMem_empty e)
  · rw [hforce]; exact hreach


end StatMech.Walls
