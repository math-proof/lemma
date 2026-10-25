/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_connopenimpconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.ReachBoxCrossing.Part2
import Def.StatisticalMechanics.Code.Walls.oc_connopenimpconn
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.RevealmentBoxCrossing

open StatMech.OSSS.ReachBoxCrossing

open StatMech.Lattice

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem oc_adj_site0_site1 : (hypercubicLattice 1).Adj oc_site0 oc_site1 := by
  rw [hypercubicLattice_adj]
  simp [oc_site0, oc_site1]


theorem oc_witness_hcoh : ∀ e, oc_witnessEdge e = s(oc_witnessEndU e, oc_witnessEndV e) :=
  fun _ => rfl


theorem oc_witness_hadj :
    ∀ e, (hypercubicLattice 1).Adj (oc_witnessEndU e) (oc_witnessEndV e) :=
  fun _ => oc_adj_site0_site1


theorem oc_witness_hinj : Function.Injective oc_witnessEdge := by
  intro a b _; exact Subsingleton.elim a b


theorem oc_connectedToSet_witness :
    ConnectedToSet 1 (liftCfg oc_witnessEdge (fun _ => true)) oc_site0
      ({oc_site1} : Set (Site 1)) := by
  have hopen : ConnOpenSet oc_witnessEndU oc_witnessEndV (fun _ => true) oc_site0
      ({oc_site1} : Set (Site 1)) := by
    refine ⟨oc_site1, Set.mem_singleton _, ?_⟩
    refine ReachOpen.step 0 rfl (Or.inl ⟨rfl, rfl⟩) ?_
    exact ReachOpen.refl oc_site1
  exact oc_connOpenSet_imp_connectedToSet oc_witness_hinj oc_witness_hcoh oc_witness_hadj hopen


theorem oc_site0_ne_site1 : oc_site0 ≠ oc_site1 := by
  intro h
  have : (oc_site0 0 : ℤ) = oc_site1 0 := by rw [h]
  simp [oc_site0, oc_site1] at this

end Walls
end StatMech
