module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
public import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerClose.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
public import Theorem.StatisticalMechanics.Code.Walls.bc_cutmeetsaxis
public import Theorem.StatisticalMechanics.Code.Walls.bc_mouthcorridor
public import Theorem.StatisticalMechanics.Code.Walls.bc_raydisjoint
public import Theorem.StatisticalMechanics.Code.Walls.bc_forcemono
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}


def bc_NearAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) : Prop :=
  hrHD_rayPt j 1 ∈ cluster d ω x ∧
    Connected d (removeSite 0 ω) (hrHD_rayPt j 1) x ∧
    (cluster d (removeSite 0 ω) x).Infinite


end Walls
end StatMech
