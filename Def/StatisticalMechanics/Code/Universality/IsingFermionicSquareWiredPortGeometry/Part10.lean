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
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredSlotRingActive (n : Nat)
    (x : FKIsingSquareWiredSlotCarrier n) : Prop :=
  fkIsingSquareWiredPortSlotTurn x.2 = .counterclockwise ∨
    ¬fkIsingSquareWiredSlotAvailable n x


noncomputable def fkIsingSquareWiredSlotRingGraph (n : Nat) :
    SimpleGraph (FKIsingSquareWiredSlotCarrier n) where
  Adj x y := ∃ u i, fkIsingSquareWiredSlotRingActive n (u, i) ∧
    ((x = (u, i) ∧ y = (u, i + 1)) ∨
      (y = (u, i) ∧ x = (u, i + 1)))
  symm := by
    constructor
    rintro x y ⟨u, i, hi, h | h⟩
    · exact ⟨u, i, hi, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨u, i, hi, Or.inl ⟨h.1, h.2⟩⟩
  loopless := by
    constructor
    rintro x ⟨u, i, _, h | h⟩
    · have hi := congrArg Prod.snd (h.1.symm.trans h.2)
      fin_cases i <;> simp at hi
    · have hi := congrArg Prod.snd (h.2.symm.trans h.1)
      fin_cases i <;> simp at hi


noncomputable def fkIsingSquareWiredSlotLocalGraph
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareWiredSlotCarrier n) where
  Adj x y := ∃ d,
    (x = fkIsingSquareWiredDartSlot n d ∧
      y = fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d)) ∨
    (y = fkIsingSquareWiredDartSlot n d ∧
      x = fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d))
  symm := by
    constructor
    rintro x y ⟨d, h | h⟩
    · exact ⟨d, Or.inr ⟨h.1, h.2⟩⟩
    · exact ⟨d, Or.inl ⟨h.1, h.2⟩⟩
  loopless := by
    constructor
    rintro x ⟨d, h | h⟩
    · have heq := fkIsingSquareWiredDartSlot_injective n
        (h.1.symm.trans h.2)
      exact (fkIsingSquare_localMate_cornerTurn_ne n omega d)
        (congrArg (fun f => (fkIsingSquareSideCorner f.2).2) heq).symm
    · have heq := fkIsingSquareWiredDartSlot_injective n
        (h.2.symm.trans h.1)
      exact (fkIsingSquare_localMate_cornerTurn_ne n omega d)
        (congrArg (fun f => (fkIsingSquareSideCorner f.2).2) heq)


end
end StatMech.Universality
