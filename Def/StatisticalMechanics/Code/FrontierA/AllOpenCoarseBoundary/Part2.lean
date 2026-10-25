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
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


noncomputable def faithfulAllOpenTrifIndicesInBox
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) : Finset (Site 2) := by
  classical
  exact (box_finite 2 N).toFinset.filter (FaithfulAllOpenTrifAt omega L)

end StatMech.FrontierA
