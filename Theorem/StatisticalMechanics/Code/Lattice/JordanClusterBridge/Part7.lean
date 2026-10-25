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
import Def.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part6
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcb_Lcyc_edge_card : jcb_Lcyc.edgeSet.ncard = 8 := by
  rw [Set.ncard_eq_toFinset_card']; decide


theorem jcb_Lcyc_connected : jcb_Lcyc.Connected := by
  rw [connected_iff]
  refine ⟨?_, ⟨0⟩⟩
  have step : ∀ i : Fin 8, jcb_Lcyc.Reachable 0 i := by
    have r01 : jcb_Lcyc.Adj 0 1 := by decide
    have r12 : jcb_Lcyc.Adj 1 2 := by decide
    have r23 : jcb_Lcyc.Adj 2 3 := by decide
    have r34 : jcb_Lcyc.Adj 3 4 := by decide
    have r45 : jcb_Lcyc.Adj 4 5 := by decide
    have r56 : jcb_Lcyc.Adj 5 6 := by decide
    have r67 : jcb_Lcyc.Adj 6 7 := by decide
    intro i
    fin_cases i
    · exact Reachable.refl _
    · exact r01.reachable
    · exact r01.reachable.trans r12.reachable
    · exact r01.reachable.trans (r12.reachable.trans r23.reachable)
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans r34.reachable))
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans
        (r34.reachable.trans r45.reachable)))
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans
        (r34.reachable.trans (r45.reachable.trans r56.reachable))))
    · exact r01.reachable.trans (r12.reachable.trans (r23.reachable.trans
        (r34.reachable.trans (r45.reachable.trans (r56.reachable.trans r67.reachable)))))
  intro i j
  exact (step i).symm.trans (step j)


theorem jcb_Lshape_nullity_one : nullity jcb_LPce.G = 1 := by
  refine jcb_nullity_eq_one_of_connected_card_eq jcb_LPce.G jcb_Lcyc_connected ?_
  show jcb_Lcyc.edgeSet.ncard = Nat.card (Fin 8)
  rw [jcb_Lcyc_edge_card, Nat.card_eq_fintype_card, Fintype.card_fin]


theorem jcb_Lshape_uniqueBoundedRegion : Nat.card (jcb_BoundedRegion jcb_LPce) = 1 :=
  jcb_boundedRegion_card_eq_one_of_nullity_one jcb_LPce jcb_Lshape_nullity_one


end Lattice
end StatMech
