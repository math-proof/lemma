/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOffdiagSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCutParity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaBound.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOffdiagSwitching.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagSeamSelector_positive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    0 < (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentSeamEdge sites
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) := by
  unfold lpReplicaOffdiagSeamSelector
  simp only [lpReplicaCurrentEdgeFlux_ofEdgeFun]
  rw [dif_pos hsrc]
  exact Classical.choose_spec
    (lpReplicaCurrent_exists_positiveSeam_of_offdiagSource
      G sites hsite hij m hsrc)

theorem lpReplicaOffdiagSeamSelector_connected
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : StatMech.Sharpness.sources (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    CurrentConnected (lpReplicaCurrentGraph G sites)
      (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
      (lpReplicaCurrentLeft sites
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m)))
      (lpReplicaCurrentRight sites
        (lpReplicaOffdiagSeamSelector G sites hsite i j hij
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m))) := by
  let k := lpReplicaOffdiagSeamSelector G sites hsite i j hij
    (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
  have hk := lpReplicaOffdiagSeamSelector_positive
    G sites hsite hij m hsrc
  refine SimpleGraph.Adj.reachable ?_
  constructor
  · unfold lpReplicaCurrentLeft lpReplicaCurrentRight
    rw [lpReplicaCurrentGraph_adj_left_right_iff]
    exact ⟨k, rfl, rfl⟩
  · simpa only [k] using hk

set_option maxHeartbeats 1600000 in

theorem lp_gatedSourcePairSum_partition_fintype
    {W L : Type*} [Fintype W] [DecidableEq W]
    [Fintype L] [DecidableEq L]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 W -> Real)
    (A B : Finset W) (P : Current W -> Prop) [DecidablePred P]
    (f : Current W -> L) :
    gatedSourcePairSum G beta J A B P =
      ∑ l : L, gatedSourcePairSum G beta J A B
        (fun n => f n = l ∧ P n) := by
  unfold gatedSourcePairSum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset L))
    (f := fun l (pq : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat)) =>
      (if StatMech.Sharpness.sources G (ofEdgeFun G pq.1) = A
        then weight G beta J (ofEdgeFun G pq.1) else 0) *
      (if StatMech.Sharpness.sources G (ofEdgeFun G pq.2) = B
        then weight G beta J (ofEdgeFun G pq.2) else 0) *
      (if f (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) = l ∧
          P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0))
    (fun l _ => summable_gatedSourcePairSummand G beta J A B
      (fun n => f n = l ∧ P n))]
  apply tsum_congr
  rintro ⟨p, q⟩
  let n := ofEdgeFun G (fun e => p e + q e)
  by_cases hp : StatMech.Sharpness.sources G (ofEdgeFun G p) = A <;>
    by_cases hq : StatMech.Sharpness.sources G (ofEdgeFun G q) = B <;>
    by_cases hP : P n <;> simp [n, hp, hq, hP]


end
end StatMech.Ising
