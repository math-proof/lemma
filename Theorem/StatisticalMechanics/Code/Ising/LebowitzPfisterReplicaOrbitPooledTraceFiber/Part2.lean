/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledTraceIndex G sites q,
        (lpReplicaOffdiagPooledSourceTraceFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledSourceTraceFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledTraceIndex G sites q))) (by
          intro z _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledSourceTraceIndex G sites i j q z))

theorem lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledTraceIndex G sites q,
        (lpReplicaOffdiagPooledTargetTraceFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledTargetTraceFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledTraceIndex G sites q))) (by
          intro y _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledTargetTraceIndex G sites i j q y))


theorem lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : ∀ u : LPReplicaOffdiagPooledTraceIndex G sites q,
      (lpReplicaOffdiagPooledSourceTraceFiber G sites i j q u).card <=
        (lpReplicaOffdiagPooledTargetTraceFiber G sites i j q u).card) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  rw [lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers,
    lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers]
  exact Finset.sum_le_sum fun u _ => hcard u


theorem lpReplicaOffdiagOrbitAtomCardInequality_of_pooledTraceFiberInjections
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : ∀ u : LPReplicaOffdiagPooledTraceIndex G sites q,
      ∃ move :
          {z // z ∈ lpReplicaOffdiagPooledSourceTraceFiber
            G sites i j q u} ->
          {y // y ∈ lpReplicaOffdiagPooledTargetTraceFiber
            G sites i j q u},
        Function.Injective move) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  have hcard : Fintype.card
      (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
    apply lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards
    intro u
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
