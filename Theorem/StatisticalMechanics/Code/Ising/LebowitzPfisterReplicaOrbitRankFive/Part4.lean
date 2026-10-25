/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_erased_union_saturated_card_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive
      G sites i j q u).card ≤ 4 := by
  classical
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive
  calc
    _ ≤ (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
          G sites i j q u).card +
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
          G sites i j q u).card := Finset.card_union_le _ _
    _ ≤ 3 + 1 := Nat.add_le_add
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three
        G sites hsite hij q hcard u)
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one
        G sites hsite hij q hcard u)
    _ = 4 := rfl


theorem lpReplica_threeCopyOffdiag_exists_seamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 3)
    (hsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    (∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
      ∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let B :=
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
  have hsupport := lpReplica_threeCopyOffdiag_endpointSupport
    G sites hsite hij m K hKcard hsource
  have hsupport' : K.biUnion (fun c => (E c).toFinset) = B := by
    simpa only [E, B] using hsupport
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hex (x : LPReplicaCurrentVertex V) (hx : x ∈ B) :
      ∃ c ∈ K, x ∈ E c := by
    have hx' : x ∈ K.biUnion fun c => (E c).toFinset := by
      rw [hsupport']
      exact hx
    obtain ⟨c, hcK, hxc⟩ := Finset.mem_biUnion.mp hx'
    exact ⟨c, hcK, Sym2.mem_toFinset.mp hxc⟩
  have hg0B : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ B := by
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  have hg1B : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ B := by
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  obtain ⟨c0, hc0K, hc0ghost⟩ := hex _ hg0B
  obtain ⟨c1, hc1K, hc1ghost⟩ := hex _ hg1B
  obtain ⟨x0, hc0edge⟩ := lpReplicaCurrentEdge_eq_ghost0_left_of_mem
    G sites c0.1.1 c0.1.2 hc0ghost
  obtain ⟨x1, hc1edge⟩ := lpReplicaCurrentEdge_eq_ghost1_right_of_mem
    G sites c1.1.1 c1.1.2 hc1ghost
  have hx0B : (.inl (.inl x0) : LPReplicaCurrentVertex V) ∈ B := by
    rw [← hsupport']
    apply Finset.mem_biUnion.mpr
    exact ⟨c0, hc0K, Sym2.mem_toFinset.mpr (by
      have h : (.inl (.inl x0) : LPReplicaCurrentVertex V) ∈ c0.1.1 := by
        rw [hc0edge]
        simp
      simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using h)⟩
  have hx1B : (.inl (.inr x1) : LPReplicaCurrentVertex V) ∈ B := by
    rw [← hsupport']
    apply Finset.mem_biUnion.mpr
    exact ⟨c1, hc1K, Sym2.mem_toFinset.mpr (by
      have h : (.inl (.inr x1) : LPReplicaCurrentVertex V) ∈ c1.1.1 := by
        rw [hc1edge]
        simp
      simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using h)⟩
  have hx0 : x0 = sites i ∨ x0 = sites j := by
    have h := hx0B
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff, hsij, hsij.symm] at h
    exact h.imp And.left And.left
  have hx1 : x1 = sites i ∨ x1 = sites j := by
    have h := hx1B
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff, hsij, hsij.symm] at h
    exact h.imp And.left And.left
  have hc01 : c0 ≠ c1 := by
    intro h
    subst c1
    change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ c0.1.1 at hc1ghost
    rw [hc0edge] at hc1ghost
    simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] at hc1ghost
  have ne_c0_of_mem {a : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m} {v : LPReplicaCurrentVertex V}
      (ha : v ∈ E a) (hv : v ∉ c0.1.1) : a ≠ c0 := by
    intro h
    subst a
    exact hv ha
  have ne_c1_of_mem {a : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m} {v : LPReplicaCurrentVertex V}
      (ha : v ∈ E a) (hv : v ∉ c1.1.1) : a ≠ c1 := by
    intro h
    subst a
    exact hv ha
  have third_eq {a b : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m}
      (haK : a ∈ K) (hbK : b ∈ K)
      (ha0 : a ≠ c0) (ha1 : a ≠ c1)
      (hb0 : b ≠ c0) (hb1 : b ≠ c1) : a = b := by
    by_contra hab
    have hfour : ({c0, c1, a, b} : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m)).card = 4 := by
      simp [hc01, ha0, ha1, hb0, hb1, hab,
        Ne.symm hc01, Ne.symm ha0, Ne.symm ha1,
        Ne.symm hb0, Ne.symm hb1, Ne.symm hab]
    have hsub : ({c0, c1, a, b} : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m)) ⊆ K := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hle := Finset.card_le_card hsub
    rw [hfour, hKcard] at hle
    omega
  rcases hx0 with rfl | rfl <;> rcases hx1 with rfl | rfl
  · right
    have hLjB : lpReplicaCurrentLeft sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRjB : lpReplicaCurrentRight sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hLjB
    obtain ⟨b, hbK, hb⟩ := hex _ hRjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    exact ⟨a, haK, sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])⟩

  · exfalso
    have hRiB : lpReplicaCurrentRight sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hLjB : lpReplicaCurrentLeft sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hRiB
    obtain ⟨b, hbK, hb⟩ := hex _ hLjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    have hedge : a.1.1 = s(lpReplicaCurrentRight sites i,
        lpReplicaCurrentLeft sites j) :=
      sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])
    have hadj : (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentLeft sites j) (lpReplicaCurrentRight sites i) := by
      rw [← SimpleGraph.mem_edgeSet]
      have hm := SimpleGraph.mem_edgeFinset.mp a.1.2
      rw [hedge] at hm
      simpa only [Sym2.eq_swap] using hm
    obtain ⟨k, hkj, hki⟩ := (lpReplicaCurrentGraph_adj_left_right_iff
      G sites (sites j) (sites i)).mp hadj
    exact hsij (hki.symm.trans hkj)
  · exfalso
    have hLiB : lpReplicaCurrentLeft sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRjB : lpReplicaCurrentRight sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hLiB
    obtain ⟨b, hbK, hb⟩ := hex _ hRjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    have hedge : a.1.1 = s(lpReplicaCurrentLeft sites i,
        lpReplicaCurrentRight sites j) :=
      sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])
    have hadj : (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites j) := by
      rw [← SimpleGraph.mem_edgeSet]
      have hm := SimpleGraph.mem_edgeFinset.mp a.1.2
      rwa [hedge] at hm
    obtain ⟨k, hki, hkj⟩ := (lpReplicaCurrentGraph_adj_left_right_iff
      G sites (sites i) (sites j)).mp hadj
    exact hsij (hki.symm.trans hkj)
  · left
    have hLiB : lpReplicaCurrentLeft sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRiB : lpReplicaCurrentRight sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hLiB
    obtain ⟨b, hbK, hb⟩ := hex _ hRiB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    exact ⟨a, haK, sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])⟩


theorem lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    (∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
      ∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  exact lpReplica_threeCopyOffdiag_exists_seamCopy
    G sites hsite hij z.1.1.1 K (by simpa only [K, d] using hthree)
      d.2.2.2.2.1

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ s : LPReplicaBalancedSelector G sites
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1)
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q,
      s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
        HEq s.selector (Finset.univ \ {c}) ∧
        @HEq
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites s.profile s.selector s.tag)
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites z.1.1.1 {c}
            (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) ∧
        ∃ y : LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q,
          LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
            (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
                (Sum.inl y)).2 =
              lpReplicaOrbitFourColorSlotCrossToggle G sites q
                (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                  z.1.1.2 z.2.2 {c})
                (lpReplicaOffdiagDecoratedSourceSlotState
                  G sites i j q z) ∧
            y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
              G sites i j q s := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites m d0.1 true false
  let C := Finset.univ \ K
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hctag0 : d0.1 c = (true, false) := by
    simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcK
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Si := by rw [hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true =
        lpReplicaRowCopies G sites m d0.1 true \ {c} := by
    rw [hmove]
    ext a
    by_cases hac : a = c
    · subst a
      simp [lpReplicaRowCopies, lpReplicaToggleRows, hctag0]
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, hac]
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    apply StatMech.GrahamGHS.FourColor.connK_mono _ hconn
    rw [hrow1Eq]
    exact Finset.sdiff_subset
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hac : a = c
    · exact Or.inl hac
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      simp [hac, hatag] at ha
  have hCcard : C.card = 2 := by
    have hcopyCard : Fintype.card
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m) = 5 := by
      calc
        _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
          Fintype.card_congr
            (lpReplicaProfileCopyEquivCommonSlot G sites q m
              z.1.1.2 z.2.2)
        _ = 5 := hcard
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard]
    have hKcard : K.card = 3 := by
      simpa only [K, d0] using hthree
    omega
  obtain ⟨e0, he0C⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites i m c e0 C hc hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Sj ∆ T) q := {
    profile := m
    orbit := z.1.1.2
    tag := d.1
    gate := d.2
    orbitLabel := z.2.2
    selector := P
    falseSource := hfalseSource
    trueSource := htrueSource
    row0Disconn := hrow0Disconn
    row1Disconn := hrow1Disconn }
  refine ⟨s, rfl, HEq.rfl, HEq.rfl, heq_of_eq hmove, ?_⟩
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Si Sj T q s c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  refine ⟨lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites i j q s, Or.inl ⟨s, rfl⟩, ?_, rfl⟩
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q hfixedD]
  exact hgeneric

set_option maxHeartbeats 1200000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inl y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites m d0.1 true false
  let C := Finset.univ \ K
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hcNotK : c ∉ K := (Finset.mem_sdiff.mp hcC).2
  have hctag' : d0.1 c = (false, false) := hctag
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag']
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcSeam : c.1.1 = lpReplicaCurrentSeamEdge sites i := hck.trans hk
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hcSeam
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Si := by rw [hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hcompConst : ∀ a ∈ C, d0.1 a = d0.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hnoTrueTrue (a) : d0.1 a ≠ (true, true) := by
    intro ha
    have haNotK : a ∉ K := by
      intro haK
      have haActive : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      exact Bool.false_ne_true
        (congrArg Prod.snd (haActive.symm.trans ha))
    have haC : a ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotK⟩
    have := hcompConst a haC
    rw [ha, hctag'] at this
    simpa using congrArg Prod.fst this
  have hrow1Original : lpReplicaRowCopies G sites m d0.1 true = K := by
    ext a
    rcases ha : d0.1 a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, K, lpReplicaCurrentCopies, ha]
    exact False.elim (hnoTrueTrue a ha)
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true = insert c K := by
    rw [hmove, lpReplicaRowCopies_toggle, hrow1Original]
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    constructor <;> intro ha
    · rcases ha with ⟨haK, hac⟩ | ⟨hac, haK⟩
      · exact Or.inr haK
      · exact Or.inl hac
    · rcases ha with rfl | haK
      · exact Or.inr ⟨rfl, hcNotK⟩
      · exact Or.inl ⟨haK, fun hac => hcNotK (hac ▸ haK)⟩
  have hparallelEnds : E c = E k := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hck
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    rw [hrow1Original]
    exact (randomCurrent_connK_insert_parallel_iff E K c k hkK
      hparallelEnds lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).mp
        (hrow1Eq ▸ hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {k} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hak : a = k
    · exact Or.inl hak
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      by_cases hac : a = c
      · subst a
        exact Bool.false_ne_true (congrArg Prod.fst (hctag.symm.trans hatag))
      · simp [hac, hatag] at ha
  obtain ⟨e0, he0C⟩ : C.Nonempty := ⟨c, hcC⟩
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites i m k e0 C hk hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Sj ∆ T) q := {
    profile := m
    orbit := z.1.1.2
    tag := d.1
    gate := d.2
    orbitLabel := z.2.2
    selector := P
    falseSource := hfalseSource
    trueSource := htrueSource
    row0Disconn := hrow0Disconn
    row1Disconn := hrow1Disconn }
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hcSeam
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Si Sj T q s c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  refine ⟨lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites i j q s, Or.inl ⟨s, rfl⟩, ?_⟩
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q hfixedD]
  exact hgeneric

set_option maxHeartbeats 1200000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites j)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inr y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites m d0.1 true false
  let C := Finset.univ \ K
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hcNotK : c ∉ K := (Finset.mem_sdiff.mp hcC).2
  have hctag' : d0.1 c = (false, false) := hctag
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag']
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcSeam : c.1.1 = lpReplicaCurrentSeamEdge sites j := hck.trans hk
  have hcends : E c = s(lpReplicaCurrentLeft sites j,
      lpReplicaCurrentRight sites j) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hcSeam
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
    simpa only [Sj, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Sj := by rw [hsingle]
      _ = Si ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T
        rw [symmDiff_comm Si Sj, symmDiff_assoc Sj Si T,
          symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hcompConst : ∀ a ∈ C, d0.1 a = d0.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hnoTrueTrue (a) : d0.1 a ≠ (true, true) := by
    intro ha
    have haNotK : a ∉ K := by
      intro haK
      have haActive : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      exact Bool.false_ne_true
        (congrArg Prod.snd (haActive.symm.trans ha))
    have haC : a ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotK⟩
    have := hcompConst a haC
    rw [ha, hctag'] at this
    simpa using congrArg Prod.fst this
  have hrow1Original : lpReplicaRowCopies G sites m d0.1 true = K := by
    ext a
    rcases ha : d0.1 a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, K, lpReplicaCurrentCopies, ha]
    exact False.elim (hnoTrueTrue a ha)
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true = insert c K := by
    rw [hmove, lpReplicaRowCopies_toggle, hrow1Original]
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    constructor <;> intro ha
    · rcases ha with ⟨haK, hac⟩ | ⟨hac, haK⟩
      · exact Or.inr haK
      · exact Or.inl hac
    · rcases ha with rfl | haK
      · exact Or.inr ⟨rfl, hcNotK⟩
      · exact Or.inl ⟨haK, fun hac => hcNotK (hac ▸ haK)⟩
  have hparallelEnds : E c = E k := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hck
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    rw [hrow1Original]
    exact (randomCurrent_connK_insert_parallel_iff E K c k hkK
      hparallelEnds lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).mp
        (hrow1Eq ▸ hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {k} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hak : a = k
    · exact Or.inl hak
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      by_cases hac : a = c
      · subst a
        exact Bool.false_ne_true (congrArg Prod.fst (hctag.symm.trans hatag))
      · simp [hac, hatag] at ha
  obtain ⟨e0, he0C⟩ : C.Nonempty := ⟨c, hcC⟩
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites j m k e0 C hk hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Si ∆ T) q := {
    profile := m
    orbit := z.1.1.2
    tag := d.1
    gate := d.2
    orbitLabel := z.2.2
    selector := P
    falseSource := hfalseSource
    trueSource := htrueSource
    row0Disconn := hrow0Disconn
    row1Disconn := hrow1Disconn }
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hcSeam
  let s' : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      change LPReplicaRowGate G sites s.profile (Sj ∆ Si ∆ T) ∅ s.tag
      rw [symmDiff_comm Sj Si]
      exact s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Sj Si T q s' c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
  let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'
  refine ⟨y, Or.inr ⟨s', rfl⟩, ?_⟩
  change (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
    (Sum.inl y)).2 = _
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold y lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
    ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q hfixedD]
  exact hgeneric


set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites j) :
    ∃ s : LPReplicaBalancedSelector G sites
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1)
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q,
      s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
        HEq s.selector (Finset.univ \ {c}) ∧
        @HEq
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites s.profile s.selector s.tag)
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites z.1.1.1 {c}
            (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) ∧
        ∃ y : LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q,
          LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧
            (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
                (Sum.inr y)).2 =
              lpReplicaOrbitFourColorSlotCrossToggle G sites q
                (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                  z.1.1.2 z.2.2 {c})
                (lpReplicaOffdiagDecoratedSourceSlotState
                  G sites i j q z) ∧
            ∃ s' : LPReplicaBalancedSelector G sites
                (lpMatchingSeamSource
                      (lpReplicaCurrentLeft sites)
                      (lpReplicaCurrentRight sites) j ∆
                    lpMatchingSeamSource
                      (lpReplicaCurrentLeft sites)
                      (lpReplicaCurrentRight sites) i ∆
                    lpMatchingGhostSource
                      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                      lpReplicaCurrentGhost1)
                (lpMatchingSeamSource
                      (lpReplicaCurrentLeft sites)
                      (lpReplicaCurrentRight sites) i ∆
                    lpMatchingGhostSource
                      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                      lpReplicaCurrentGhost1) q,
              y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
                  G sites j i q s' ∧
                s'.profile = s.profile ∧
                HEq s'.selector s.selector ∧ HEq s'.tag s.tag := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites m d0.1 true false
  let C := Finset.univ \ K
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hctag0 : d0.1 c = (true, false) := by
    simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcK
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites j,
      lpReplicaCurrentRight sites j) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
    simpa only [Sj, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hBswap : B = Sj ∆ Si ∆ T := by
    change Si ∆ Sj ∆ T = Sj ∆ Si ∆ T
    rw [symmDiff_comm Si Sj]
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Sj := by rw [hsingle]
      _ = Si ∆ T := by
        rw [hBswap, symmDiff_assoc Sj Si T,
          symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true =
        lpReplicaRowCopies G sites m d0.1 true \ {c} := by
    rw [hmove]
    ext a
    by_cases hac : a = c
    · subst a
      simp [lpReplicaRowCopies, lpReplicaToggleRows, hctag0]
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, hac]
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    apply StatMech.GrahamGHS.FourColor.connK_mono _ hconn
    rw [hrow1Eq]
    exact Finset.sdiff_subset
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hac : a = c
    · exact Or.inl hac
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      simp [hac, hatag] at ha
  have hCcard : C.card = 2 := by
    have hcopyCard : Fintype.card
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m) = 5 := by
      calc
        _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
          Fintype.card_congr
            (lpReplicaProfileCopyEquivCommonSlot G sites q m
              z.1.1.2 z.2.2)
        _ = 5 := hcard
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard]
    have hKcard : K.card = 3 := by
      simpa only [K, d0] using hthree
    omega
  obtain ⟨e0, he0C⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites j m c e0 C hc hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Si ∆ T) q := {
    profile := m
    orbit := z.1.1.2
    tag := d.1
    gate := d.2
    orbitLabel := z.2.2
    selector := P
    falseSource := hfalseSource
    trueSource := htrueSource
    row0Disconn := hrow0Disconn
    row1Disconn := hrow1Disconn }
  refine ⟨s, rfl, HEq.rfl, HEq.rfl, heq_of_eq hmove, ?_⟩
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hc
  let s' : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      change LPReplicaRowGate G sites s.profile (Sj ∆ Si ∆ T) ∅ s.tag
      rw [symmDiff_comm Sj Si]
      exact s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Sj Si T q s' c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
  let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'
  refine ⟨y, Or.inr ⟨s', rfl⟩, ?_,
    ⟨s', rfl, rfl, HEq.rfl, HEq.rfl⟩⟩
  change (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
    (Sum.inl y)).2 = _
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold y lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
    ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q hfixedD]
  exact hgeneric


end
end StatMech.Ising
