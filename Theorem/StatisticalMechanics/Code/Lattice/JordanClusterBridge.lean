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
import Def.StatisticalMechanics.Code.Lattice.JordanClusterBridge
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcb_boundedRegion_card_eq_nullity (P : PlanarZ2Subgraph) :
    Nat.card (jcb_BoundedRegion P) = nullity P.G := by
  rw [Nat.card_eq_of_bijective _ (jcb_boundedRegionEquiv P).bijective, Nat.card_eq_fintype_card,
    Fintype.card_fin]


theorem jcb_nullity_eq_one_of_connected_card_eq {V : Type} [Finite V] (G : SimpleGraph V)
    (hconn : G.Connected) (hcard : G.edgeSet.ncard = Nat.card V) :
    nullity G = 1 := by
  classical
  have hbound := card_le_edgeSet_add_components G
  have hcomp : Nat.card G.ConnectedComponent = 1 := card_components_eq_one_of_connected hconn
  unfold nullity
  rw [hcard, hcomp]
  have hpos : 0 < Nat.card V := by
    haveI : Nonempty V := hconn.nonempty
    exact Nat.card_pos
  omega


end Lattice
end StatMech
