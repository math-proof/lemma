module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
public import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
public import Def.StatisticalMechanics.Code.Walls.pwwbdedge
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


theorem pww_a_adj_b : (hypercubicLattice 2).Adj pww_a pww_b := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two, pww_a, pww_b]


end Walls
end StatMech
