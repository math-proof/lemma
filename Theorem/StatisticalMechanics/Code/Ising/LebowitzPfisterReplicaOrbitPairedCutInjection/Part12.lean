/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part11
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoRightPairedCuts
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hcuts : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
        G sites i j q hcard z) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
    G sites i j q
      (lpReplicaOffdiagDecoratedOrbitInjectionOfFixedMaskTargetRealizations
        G sites i j q
          (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
          (fun z =>
            lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target
              G sites i j q hcard z (hcuts z)))


theorem LPReplicaOffdiagCoupledPairedCrossToggleInjection.output_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    Function.Injective s.output := by
  have hcross :=
    lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable
      G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q)
      s.selector s.output
      (lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q) (by
        intro z w h
        exact s.collision_stable z w (congrArg Prod.fst h))
  intro z w houtput
  apply hcross
  apply Prod.ext
  · exact houtput
  · change lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (s.selector z)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (s.selector w)
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)
    rw [<- s.output_state z, <- s.output_state w, houtput]


theorem lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
  let move : LPReplicaOffdiagDecoratedSource G sites i j q ->
      {y // y ∈ lpReplicaOffdiagCoupledPairedOutputs G sites i j q} :=
    fun z => ⟨s.output z, by
      simp only [lpReplicaOffdiagCoupledPairedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact s.output_valid z⟩
  have hmove : Function.Injective move := by
    intro z w h
    apply s.output_injective G sites i j q
    exact congrArg Subtype.val h
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective move hmove


theorem lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q P
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
    G sites i j q
      (lpReplicaOffdiagCoupledPairedCrossToggleInjectionOfFixedMaskRealizations
        G sites i j q P hrealize)


theorem lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalFirstTwoRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard)
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations
    G sites i j q
      (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard) hrealize


theorem lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
        LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
              (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations
    G sites i j q
      (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) hrealize


theorem lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoPairedCuts
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (hcuts : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable
        G sites i j q hcard z) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card :=
  lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations
    G sites i j q hcard fun z =>
      lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target
        G sites i j q hcard z (hcuts z)


theorem lpReplicaOffdiagCoupledPairedHall_of_crossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    LPReplicaOffdiagCoupledPairedHall G sites i j q := by
  rw [lpReplicaOffdiagCoupledPairedHall_iff_outputCard]
  exact lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
    G sites i j q s


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedCrossToggleInjection
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOffdiagCoupledPairedCrossToggleInjection
      G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    G sites i j q
      (lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection
        G sites i j q s)

end
end StatMech.Ising
