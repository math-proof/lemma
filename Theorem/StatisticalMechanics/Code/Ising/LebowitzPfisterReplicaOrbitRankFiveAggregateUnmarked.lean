/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCollisionAllocation.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateUnmarked
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem LPReplicaOffdiagDecoratedSource.resolvable_or_unmarkedSaturated_of_highRow
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
      G sites i j q z) :
    LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
        G sites i j q z ∨
      LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
        G sites i j q z := by
  classical
  by_cases hsat : LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive
      G sites i j q z
  · by_cases hi : exists c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
        c.1.1 = lpReplicaCurrentSeamEdge sites i
    · exact Or.inl ⟨hhigh, fun _ => Or.inl hi⟩
    · by_cases hj : exists c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
          c.1.1 = lpReplicaCurrentSeamEdge sites j
      · exact Or.inl ⟨hhigh, fun _ => Or.inr hj⟩
      · simp only [not_exists] at hi hj
        exact Or.inr ⟨hsat, hi, hj⟩
  · exact Or.inl ⟨hhigh, fun hs => (hsat hs).elim⟩


theorem LPReplicaOffdiagDecoratedSource.low_or_resolvable_or_unmarkedSaturated_rankFive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q z ∨
      LPReplicaOffdiagDecoratedSource.IsResolvableHighRowRankFive
          G sites i j q z ∨
        LPReplicaOffdiagDecoratedSource.IsUnmarkedSaturatedRankFive
          G sites i j q z := by
  classical
  let u := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z
  have hz : z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u := by
    simp [lpReplicaOffdiagDecoratedSourceCrossTraceFiber, u]
  rw [lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
    G sites hsite hij q hcard u] at hz
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive at hz
  rcases Finset.mem_union.mp hz with hlow | hhigh
  · exact Or.inl (Finset.mem_filter.mp hlow).2
  · rcases LPReplicaOffdiagDecoratedSource.resolvable_or_unmarkedSaturated_of_highRow
        G sites i j q z (Finset.mem_filter.mp hhigh).2 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)


end
end StatMech.Ising
