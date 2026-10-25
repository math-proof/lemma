/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_centralFaceContactSubwalk {H : SimpleGraph (Site 2)}
    {f g x y : Site 2} (a : H.Walk f g)
    (hx : x ∈ a.support) (hy : y ∈ a.support) : H.Walk x y :=
  (a.takeUntil x hx).reverse.append (a.takeUntil y hy)

end
end StatMech.Universality
