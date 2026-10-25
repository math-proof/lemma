/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part15


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredExpandedAdj_symm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Symmetric (fkIsingSquareWiredExpandedAdj n hn omega) := by
  intro x y h
  rcases h with h | h | h
  · rcases h with ⟨a, b, rfl, rfl, hab⟩
    exact Or.inl ⟨b, a, rfl, rfl, hab.symm⟩
  · rcases h with ⟨a, b, rfl, rfl, ha, hb, hab⟩
    exact Or.inr (Or.inl ⟨b, a, rfl, rfl, hb, ha, hab.symm⟩)
  · exact Or.inr (Or.inr (by simpa only [Sym2.eq_swap] using h))

theorem fkIsingSquareWiredExpandedAdj_irrefl
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Irreflexive (fkIsingSquareWiredExpandedAdj n hn omega) := by
  intro x h
  rcases h with h | h | h
  · rcases h with ⟨a, b, hxa, hxb, hab⟩
    have habEq : a = b := Sum.inl.inj (hxa.symm.trans hxb)
    subst b
    exact (fkIsingSquareWiredSlotLocalGraph n omega).irrefl hab
  · rcases h with ⟨a, b, hxa, hxb, _, _, hab⟩
    have habEq : a = b := Sum.inl.inj (hxa.symm.trans hxb)
    subst b
    exact (fkIsingSquareWiredSlotRingGraph n).irrefl hab
  · rcases h with ⟨k, h | h | h⟩ <;> rw [Sym2.eq_iff] at h
    · rcases h with h | h
      · have hc := h.1.symm.trans h.2
        cases hc
      · have hc := h.2.symm.trans h.1
        cases hc
    · rcases h with h | h
      · have hc := h.1.symm.trans h.2
        cases hc
      · have hc := h.2.symm.trans h.1
        cases hc
    · rcases h with h | h
      · have heq := Sum.inl.inj (h.1.symm.trans h.2)
        have hi := congrArg Prod.snd heq
        have hiv := congrArg Fin.val hi
        norm_num at hiv
      · have heq := Sum.inl.inj (h.2.symm.trans h.1)
        have hi := congrArg Prod.snd heq
        have hiv := congrArg Fin.val hi
        norm_num at hiv


end
end StatMech.Universality
