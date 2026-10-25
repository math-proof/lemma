/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[reducible] noncomputable def jcb_uniqueBoundedRegion_of_connected_cycle (P : PlanarZ2Subgraph)
    (hconn : P.G.Connected) (hcard : P.G.edgeSet.ncard = Nat.card P.V) :
    Unique (jcb_BoundedRegion P) :=
  jcb_uniqueBoundedRegion_of_nullity_one P
    (jcb_nullity_eq_one_of_connected_card_eq P.G hconn hcard)


end Lattice
end StatMech
