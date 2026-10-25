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
import Instance.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcb_cyc4_edge_card : jbc_cyc4.edgeSet.ncard = 4 := by
  rw [Set.ncard_eq_toFinset_card']; decide


theorem jcb_cyc4_connected : jbc_cyc4.Connected := by
  rw [connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  have h01 : jbc_cyc4.Reachable 0 1 := (show jbc_cyc4.Adj 0 1 by decide).reachable
  have h03 : jbc_cyc4.Reachable 0 3 := (show jbc_cyc4.Adj 0 3 by decide).reachable
  have h32 : jbc_cyc4.Reachable 3 2 := (show jbc_cyc4.Adj 3 2 by decide).reachable
  have h02 : jbc_cyc4.Reachable 0 2 := h03.trans h32
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact Reachable.refl _
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h03 | exact h03.symm
      | exact h01.symm.trans h02 | exact h02.symm.trans h01
      | exact h01.symm.trans h03 | exact h03.symm.trans h01
      | exact h02.symm.trans h03 | exact h03.symm.trans h02


theorem jcb_square_nullity_one : nullity jbc_Pce.G = 1 := by
  refine jcb_nullity_eq_one_of_connected_card_eq jbc_Pce.G jcb_cyc4_connected ?_
  show jbc_cyc4.edgeSet.ncard = Nat.card (Fin 4)
  rw [jcb_cyc4_edge_card, Nat.card_eq_fintype_card, Fintype.card_fin]


theorem jcb_square_uniqueBoundedRegion : Nat.card (jcb_BoundedRegion jbc_Pce) = 1 :=
  jcb_boundedRegion_card_eq_one_of_nullity_one jbc_Pce jcb_square_nullity_one


end Lattice
end StatMech
