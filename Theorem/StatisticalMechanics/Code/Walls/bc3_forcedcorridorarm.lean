/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_corridorArm_chain (j : Fin d) (L : ℕ) (G : Finset (Sym2 (Site d)))
    (hsub : hrHD_corridorEdges j (L + 1) ⊆ G) :
    Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) :=
  bc2_corridorChain_in_union j L G hsub


theorem bc3_corridorArm_infinite (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (G : Finset (Sym2 (Site d)))
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite) :
    (cluster d (removeSite 0 (forceOpenFinset G ω)) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite :=
  bc2_clusterInfinite_force_mono_origin ω G hinf


end Walls
end StatMech
