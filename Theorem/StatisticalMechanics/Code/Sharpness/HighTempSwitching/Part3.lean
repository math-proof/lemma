/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Structure.StatisticalMechanics.Code.Sharpness.HighTempSwitching
open Finset
open scoped symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem exists_highTempFirstExit (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Finset (Sym2 V)) (hK : K ⊆ G.edgeFinset) {o z : V}
    (hbd : HasOddBoundary K (sourcePair o z)) (S : Finset V)
    (ho : o ∈ S) (hz : z ∉ S) :
    Nonempty (HighTempFirstExit K o z S) := by
  have hoz : o ≠ z := fun h => hz (h ▸ ho)
  have hbd' : HasOddBoundary K {o, z} := by
    rwa [sourcePair_eq_pair hoz] at hbd
  let p := (hasOddBoundary_backbone G K hK hoz hbd').some
  obtain ⟨k, hk1, hkle, hx, hy, _heG, hodd, _hpos, hprev⟩ :=
    backbone_firstExit G p S ho hz
  let x := p.1.getVert (k - 1)
  let y := p.1.getVert k
  let qwalk := p.1.take (k - 1)
  let Q := qwalk.edges.toFinset
  have hQsub : Q ⊆ K := by
    intro e he
    have heList : e ∈ qwalk.edges := by simpa [Q] using he
    have hePath : e ∈ p.1.edges := by
      change e ∈ (p.1.take (k - 1)).edges at heList
      rw [SimpleGraph.Walk.edges_take] at heList
      exact List.take_subset _ _ heList
    have heOdd := isBackbonePath_edge_odd G p hePath
    by_contra heK
    simp [edgeIndicatorCurrent, heK] at heOdd
  have hQinside : ∀ e ∈ Q, edgeInside S e := by
    intro e he v hv
    have heList : e ∈ qwalk.edges := by simpa [Q] using he
    have hvSupp : v ∈ qwalk.support := qwalk.mem_support_of_mem_edges heList hv
    change v ∈ (p.1.take (k - 1)).support at hvSupp
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ,
      List.mem_take_iff_getElem] at hvSupp
    obtain ⟨j, hj, hvj⟩ := hvSupp
    have hjk : j < k := by
      have : j < k - 1 + 1 := hj.trans_le (Nat.min_le_left _ _)
      omega
    have hjlen : j ≤ p.1.length := hjk.le.trans hkle
    have hget : p.1.getVert j = v := by
      rw [p.1.getVert_eq_support_getElem hjlen]
      exact hvj
    exact hget ▸ hprev j hjk
  have hQsrc : HasOddBoundary Q (sourcePair o x) := by
    have hpath : qwalk.IsPath := p.2.take (k - 1)
    simpa only [Q, qwalk, x] using hasOddBoundary_path_edges qwalk hpath
  have hexitK : s(x, y) ∈ K := by
    by_contra heK
    simp [x, y, edgeIndicatorCurrent, heK] at hodd
  have hexitQ : s(x, y) ∉ Q := by
    intro heQ
    have heTake : s(x, y) ∈ List.take (k - 1) p.1.edges := by
      have : s(x, y) ∈ (p.1.take (k - 1)).edges := by
        simpa [Q, qwalk] using heQ
      rwa [SimpleGraph.Walk.edges_take] at this
    have hi : k - 1 < p.1.length := by omega
    have hedgeEq : p.1.edges[k - 1]'(by simpa using hi) = s(x, y) := by
      simpa only [x, y, show k - 1 + 1 = k by omega] using
        walk_edge_getElem p.1 (k - 1) hi
    have heDrop : s(x, y) ∈ List.drop (k - 1) p.1.edges := by
      rw [List.drop_eq_getElem_cons (by simpa using hi), hedgeEq]
      simp
    exact (List.disjoint_take_drop p.2.isTrail.edges_nodup (le_refl (k - 1)))
      heTake heDrop
  refine ⟨⟨x, y, Q, hx, hy, hQsub, hQinside, hQsrc,
    hexitK, hexitQ, ?_⟩⟩
  exact (SimpleGraph.mem_edgeFinset.mp (hK hexitK)).ne


end Sharpness
end StatMech
