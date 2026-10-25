/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceEmbedding.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

@[simp] theorem mem_pfdEdgeBundle (P : PlanarZ2Subgraph)
    (a : Sym2 (kwg_Face P)) (e : kwg_Edge P) :
    e ∈ pfdEdgeBundle P a ↔ kwg_dualEnds P e = a := by
  simp [pfdEdgeBundle]


end
end StatMech.FrontierD
