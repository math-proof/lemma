module
public import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenContractionGeneral
public import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
public import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundaryGeneral
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


noncomputable def bgfdFaithfulAllOpenTrifIndicesInBox
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) : Finset (Site d) := by
  classical
  exact (box_finite d N).toFinset.filter (BgfdFaithfulAllOpenTrifAt omega L)

end StatMech.FrontierA
