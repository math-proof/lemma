/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualBundles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceEmbedding.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

def pfdEffectiveParam (P : PlanarZ2Subgraph) (p : Real)
    (a : Sym2 (kwg_Face P)) : Real :=
  1 - (1 - p) ^ (pfdEdgeBundle P a).card


end
end StatMech.FrontierD
