/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_self
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
      G sites q y y.1 = y := by
  rfl

@[simp] theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_flip
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y).1 =
      lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y := by
  rfl


theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hy : ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q y) (b : Fin 2) :
    ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
          G sites q y b) := by
  exact hy


theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_strictRouteCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hy : ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q y) (b : Fin 2)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
        G sites q y b ≠
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d := by
  intro hcollision
  have hb :=
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict
      G sites q y hy b
  apply hb
  rw [hcollision]
  exact
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence
      G sites hsite q hcard z d


@[simp] theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) (b : Fin 2) :
    (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
      G sites q y b).2 = y.2 := by
  rfl


theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y w : LPReplicaAggregateDecoratedTarget G sites q) (b c : Fin 2)
    (h : lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
          G sites q y b =
        lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
          G sites q w c) :
    y.2 = w.2 := by
  change (⟨b, y.2⟩ : LPReplicaAggregateDecoratedTarget G sites q) =
    ⟨c, w.2⟩ at h
  exact (Prod.mk.inj h).2


theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_of_key_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hkey : y.2 ≠ w.2) (b c : Fin 2) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
        G sites q y b ≠
      lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
        G sites q w c := by
  intro h
  exact hkey
    (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq
      G sites q y w b c h)


end
end StatMech.Ising
