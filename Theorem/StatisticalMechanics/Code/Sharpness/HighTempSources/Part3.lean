/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSources.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLieb.Part2
import Def.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
open Finset
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem incidentFlux_edgeIndicatorCurrent (F : Finset (Sym2 V))
    (hF : F ⊆ G.edgeFinset) (v : V) :
    incidentFlux G (edgeIndicatorCurrent F) v = incCount F v := by
  unfold incidentFlux edgeIndicatorCurrent incCount
  rw [Finset.card_eq_sum_ones]
  symm
  calc
    ∑ e ∈ F.filter (fun e => v ∈ e), 1 =
        ∑ e ∈ F.filter (fun e => v ∈ e), if e ∈ F then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          rw [if_pos (Finset.mem_filter.mp he).1]
    _ = ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), if e ∈ F then 1 else 0 := by
      apply Finset.sum_subset
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨hF he.1, he.2⟩
      · intro e heG heF
        rw [if_neg]
        intro he
        apply heF
        exact Finset.mem_filter.mpr ⟨he, (Finset.mem_filter.mp heG).2⟩


theorem sources_edgeIndicatorCurrent (F : Finset (Sym2 V)) (A : Finset V)
    (hF : F ⊆ G.edgeFinset) (hbd : HasOddBoundary F A) :
    sources G (edgeIndicatorCurrent F) = A := by
  ext v
  rw [mem_sources, incidentFlux_edgeIndicatorCurrent G F hF v]
  exact hbd v


theorem hasOddBoundary_backbone (F : Finset (Sym2 V)) {o z : V}
    (hF : F ⊆ G.edgeFinset) (hoz : o ≠ z)
    (hbd : HasOddBoundary F {o, z}) :
    Nonempty (IsBackbonePath G (edgeIndicatorCurrent F) o z) := by
  apply shb_backbone_exists G (edgeIndicatorCurrent F) hoz
  exact sources_edgeIndicatorCurrent G F {o, z} hF hbd


theorem hasOddBoundary_firstExit (F : Finset (Sym2 V)) {o z : V}
    (hF : F ⊆ G.edgeFinset) (hoz : o ≠ z)
    (hbd : HasOddBoundary F {o, z}) (S : Finset V) (ho : o ∈ S) (hz : z ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, s(x, y) ∈ F := by
  let p := (hasOddBoundary_backbone G F hF hoz hbd).some
  obtain ⟨k, _, _, hx, hy, _, hodd, _, _⟩ := backbone_firstExit G p S ho hz
  refine ⟨p.1.getVert (k - 1), hx, p.1.getVert k, hy, ?_⟩
  by_contra hnot
  simp [edgeIndicatorCurrent, hnot] at hodd

end Sharpness
end StatMech
