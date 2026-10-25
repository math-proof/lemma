/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q,
        (lpReplicaOffdiagPooledSourceIntermediateFiber
          G sites hsite hij q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledSourceIntermediateFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledIntermediateAtom G sites i j q))) (by
          intro z _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledSourceIntermediate
              G sites hsite hij q z))

theorem lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q,
        (lpReplicaOffdiagPooledTargetIntermediateFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledTargetIntermediateFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledIntermediateAtom G sites i j q))) (by
          intro y _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledTargetIntermediate G sites i j q y))


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_pooledIntermediateInjections
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : ∀ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q,
      ∃ move :
          {z // z ∈ lpReplicaOffdiagPooledSourceIntermediateFiber
            G sites hsite hij q u} ->
          {y // y ∈ lpReplicaOffdiagPooledTargetIntermediateFiber
            G sites i j q u},
        Function.Injective move) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  have hcard : Fintype.card
      (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
    rw [lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers
        G sites hsite hij q,
      lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers]
    apply Finset.sum_le_sum
    intro u _
    obtain ⟨move, hmove⟩ := hinj u
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective move hmove
  dsimp only [LPReplicaOffdiagOrbitAtomCardInequality]
  rw [← card_lpReplicaDecoratedOrbitAtom,
    ← card_lpReplicaDecoratedOrbitAtom,
    ← card_lpReplicaDecoratedOrbitAtom]
  simpa only [LPReplicaOffdiagDecoratedSource,
    LPReplicaOffdiagDecoratedTarget, Fintype.card_sum] using hcard


end
end StatMech.Ising
