module
public import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenContractionGeneral
public import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
public import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
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


def BgfdFaithfulAllOpenTrifAt
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j : Site d) : Prop :=
  bc67_IsGnTrifurcation omega L (bgfdCentre L j) ∧
    BgfdIndexAllOpen omega L j


end StatMech.FrontierA
