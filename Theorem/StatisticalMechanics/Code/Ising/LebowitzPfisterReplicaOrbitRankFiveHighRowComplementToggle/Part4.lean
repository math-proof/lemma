/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem nonempty_lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Nonempty (LPReplicaAggregateRankFiveSupportedStrictRouteEmbedding
      G sites hsite q hcard) := by
  classical
  let N := lpReplicaAggregateRankFiveStrictRouteNeighbors
    G sites hsite q hcard
  have hHall : ∀ S : Finset
      (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q),
      S.card ≤ (S.biUnion N).card := by
    intro S
    have h := LPReplicaAggregateRankFiveStrictRouteHall
      G sites hsite q hcard S
    have heq : S.biUnion N = Finset.univ.filter fun target :
        LPReplicaAggregateDecoratedTarget G sites q =>
          ∃ source ∈ S,
            LPReplicaAggregateRankFiveStrictRouteRelated
              G sites hsite q hcard source target := by
      ext y
      simp [N, lpReplicaAggregateRankFiveStrictRouteNeighbors]
    rw [heq]
    exact h
  obtain ⟨move, hmove, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
  refine ⟨⟨⟨move, hmove⟩, ?_⟩⟩
  intro z
  have hz := hmem z
  simpa only [N, lpReplicaAggregateRankFiveStrictRouteNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and] using hz


end
end StatMech.Ising
