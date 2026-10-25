/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary
open Finset Set SimpleGraph


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


def FaithfulAllOpenTrifAt
    (omega : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) : Prop :=
  bc67_IsGnTrifurcation omega L (bgf2_centre L j) ∧
    bgf2_IndexAllOpen omega L j


end StatMech.FrontierA
