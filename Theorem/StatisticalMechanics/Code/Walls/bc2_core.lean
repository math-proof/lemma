/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
import Theorem.StatisticalMechanics.Code.Walls.bc2_raydisjoint.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc2_corridorChain_in_union (j : Fin d) (L : ℕ) (G : Finset (Sym2 (Site d)))
    (hsub : hrHD_corridorEdges j (L + 1) ⊆ G) :
    Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
  have hchain := bc2_corridorChain j L (L + 1) (by omega) le_rfl
  have he : (((L + 1 : ℕ) : ℤ)) = ((L : ℤ) + 1) := by push_cast; ring
  rw [he] at hchain
  exact Relation.ReflTransGen.mono
    (fun u v hstep => ⟨hstep.1, hsub hstep.2.1, hstep.2.2⟩) _ _ hchain


end Walls
end StatMech
