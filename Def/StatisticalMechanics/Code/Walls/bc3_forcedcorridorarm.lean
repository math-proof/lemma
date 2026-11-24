module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
public import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc3_forcedcorridorarm
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_forcedcorridorarm.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_ForcedCorridorArm (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (G : Finset (Sym2 (Site d))) : Prop :=
  Relation.ReflTransGen (CorridorStep G) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) ∧
    (cluster d (removeSite 0 (forceOpenFinset G ω)) (hrHD_rayPt j ((L : ℤ) + 1))).Infinite


end Walls
end StatMech
