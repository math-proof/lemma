/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapFiniteGraph.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_axisGapEdgeLift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2))
    (he : e ∈ rlc_axisGapEdges G) : Sym2 (RlcConnectorVertex n) :=
  Classical.choose (rlc_axisGapEdge_exists_lift G he)

end
end StatMech.Universality
