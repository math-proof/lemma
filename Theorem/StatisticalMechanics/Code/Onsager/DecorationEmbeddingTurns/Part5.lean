/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part5


namespace StatMech.Onsager

theorem ons_decExpandedKWLoop_edgeSet
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    ons_dartEdgeSet (ons_decExpandedKWLoop L q hq) =
      (ons_decEmbedWalk L q).edges.toFinset := by
  classical
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  rw [← ons_decExpandedGeometricLoop_edgeSet L q]
  ext e
  simp only [ons_dartEdgeSet, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨-k, by simp [ons_decExpandedKWLoop]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨-k, by simp [ons_decExpandedKWLoop]⟩

theorem ons_decExpandedKWLoop_sum_exponentX
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 =
      8 * ∑ k, ons_dirExponentX (ons_decCycleDartLoop q k).2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  calc
    ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 =
        ∑ k, ons_dirExponentX
          (ons_decExpandedGeometricLoop L q k).2 := by
      change (∑ k, ons_dirExponentX
        (ons_decExpandedGeometricLoop L q (-k)).2) = _
      exact Equiv.sum_comp (Equiv.neg _)
        (fun k => ons_dirExponentX
          (ons_decExpandedGeometricLoop L q k).2)
    _ = 8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentX a.2)).sum :=
      ons_decExpandedGeometricLoop_sum_exponentX L q
    _ = _ := by
      rw [ons_decWalkExternalDarts_sum_eq_cycleDartLoop q hq hsnd]

theorem ons_decExpandedKWLoop_sum_exponentY
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 =
      8 * ∑ k, ons_dirExponentY (ons_decCycleDartLoop q k).2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  calc
    ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 =
        ∑ k, ons_dirExponentY
          (ons_decExpandedGeometricLoop L q k).2 := by
      change (∑ k, ons_dirExponentY
        (ons_decExpandedGeometricLoop L q (-k)).2) = _
      exact Equiv.sum_comp (Equiv.neg _)
        (fun k => ons_dirExponentY
          (ons_decExpandedGeometricLoop L q k).2)
    _ = 8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentY a.2)).sum :=
      ons_decExpandedGeometricLoop_sum_exponentY L q
    _ = _ := by
      rw [ons_decWalkExternalDarts_sum_eq_cycleDartLoop q hq hsnd]

theorem ons_decExpandedKWLoop_valid
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∀ k : Fin (ons_decExpandedDartList L q).length,
      (ons_decExpandedKWLoop L q hq k).1 =
        ons_dirStep (8 * L) (ons_decExpandedKWLoop L q hq (k + 1)).2
          (ons_decExpandedKWLoop L q hq (k + 1)).1 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  intro k
  have h := ons_decExpandedGeometricLoop_valid L q hq (-(k + 1))
  have hi : -(k + 1) + 1 = -k := by abel
  rw [hi] at h
  simpa [ons_decExpandedKWLoop] using h.symm

theorem ons_decExpandedKWLoop_site_injective
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    Function.Injective
      (fun k : Fin (ons_decExpandedDartList L q).length =>
        (ons_decExpandedKWLoop L q hq k).1) := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  intro i j hij
  have hneg : -i = -j :=
    ons_decExpandedGeometricLoop_site_injective L q hq (by
      simpa [ons_decExpandedKWLoop] using hij)
  exact neg_injective hneg

theorem ons_decExpandedKWLoop_site_mem_embedSupport
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (k : Fin (ons_decExpandedDartList L q).length) :
    (ons_decExpandedKWLoop L q hq k).1 ∈
      (ons_decEmbedWalk L q).support := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hmem : ons_decExpandedGeometricLoop L q (-k) ∈
      ons_decExpandedDartList L q :=
    List.get_mem _ (-k)
  have hsite : (ons_decExpandedGeometricLoop L q (-k)).1 ∈
      (ons_decExpandedDartList L q).map (fun a => a.1) :=
    List.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [ons_decExpandedDartList_sites] at hsite
  apply List.mem_of_mem_dropLast
  simpa [ons_decExpandedKWLoop] using hsite

theorem ons_decExpandedKWLoop_sites_disjoint
    (L : ℕ) [Fact (2 < L)]
    {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (p : (ons_decGraph L).Walk e e)
    (hq : q.IsCycle) (hp : p.IsCycle)
    (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
    ∀ (i : Fin (ons_decExpandedDartList L q).length)
      (j : Fin (ons_decExpandedDartList L p).length),
      (ons_decExpandedKWLoop L q hq i).1 ≠
        (ons_decExpandedKWLoop L p hp j).1 := by
  have hsupp :=
    ons_decEmbedWalk_support_disjoint_of_toSubgraph L q p hdisj
  intro i j
  intro hij
  apply (List.disjoint_left.mp hsupp)
    (ons_decExpandedKWLoop_site_mem_embedSupport L q hq i)
  rw [hij]
  exact ons_decExpandedKWLoop_site_mem_embedSupport L p hp j

theorem ons_decExpandedKWLoop_nonUturn
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∀ k : Fin (ons_decExpandedDartList L q).length,
      (ons_decExpandedKWLoop L q hq k).2 ≠
        (ons_decExpandedKWLoop L q hq (k + 1)).2 + 2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  let v := ons_decExpandedKWLoop L q hq
  have hvalid := ons_decExpandedKWLoop_valid L q hq
  have hinj := ons_decExpandedKWLoop_site_injective L q hq
  have hn : 2 < (ons_decExpandedDartList L q).length := by
    have := ons_decExpandedDartList_length_pos L q hq
    rw [ons_decExpandedDartList_length]
    have hqthree := hq.three_le_length
    omega
  have htwo : (2 : Fin (ons_decExpandedDartList L q).length) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change 2 % (ons_decExpandedDartList L q).length = 0 at hv
    rw [Nat.mod_eq_of_lt hn] at hv
    omega
  intro k hdir
  have hprev := hvalid (k - 1)
  have heq : (v (k - 1)).1 = (v (k + 1)).1 := by
    calc
      (v (k - 1)).1 = ons_dirStep (8 * L) (v k).2 (v k).1 := by
        simpa [v] using hprev
      _ = ons_dirStep (8 * L) ((v (k + 1)).2 + 2)
          (ons_dirStep (8 * L) (v (k + 1)).2 (v (k + 1)).1) := by
        rw [hdir, hvalid k]
      _ = (v (k + 1)).1 :=
        ons_dirStep_opposite (8 * L) (v (k + 1)).2 (v (k + 1)).1
  have hidx : k - 1 = k + 1 := hinj heq
  have hm : (-1 : Fin (ons_decExpandedDartList L q).length) = 1 := by
    calc
      -1 = -k + (k - 1) := by abel
      _ = -k + (k + 1) := by rw [hidx]
      _ = 1 := by abel
  apply htwo
  calc
    (2 : Fin (ons_decExpandedDartList L q).length) = 1 + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    _ = -1 + 1 := by rw [hm]
    _ = 0 := neg_add_cancel 1


theorem ons_decEmbedWalk_evenHomology_eq
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_evenHomology (8 * L) (ons_decEmbedWalk L q).edges.toFinset =
      ons_evenHomology L (ons_walkOriginalEdges q) := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  let loop := ons_decCycleDartLoop q
  have hvalid := ons_decCycleDartLoop_valid q hq hsnd
  obtain ⟨mx, my, hmx, hmy⟩ := ons_loop_winding_exists loop hvalid
  have hmxRefined :
      (∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2) =
        ((8 * L : ℕ) : ℤ) * mx := by
    rw [ons_decExpandedKWLoop_sum_exponentX L q hq hsnd]
    change 8 * (∑ k, ons_dirExponentX (loop k).2) = _
    rw [hmx]
    push_cast
    ring
  have hmyRefined :
      (∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2) =
        ((8 * L : ℕ) : ℤ) * my := by
    rw [ons_decExpandedKWLoop_sum_exponentY L q hq hsnd]
    change 8 * (∑ k, ons_dirExponentY (loop k).2) = _
    rw [hmy]
    push_cast
    ring
  have hrefined :=
    ons_evenHomology_dartEdgeSet_eq_windingParity
      (ons_decExpandedKWLoop L q hq)
      (ons_decExpandedKWLoop_valid L q hq)
      (ons_decExpandedKWLoop_site_injective L q hq)
      (ons_decExpandedKWLoop_nonUturn L q hq)
      mx my hmxRefined hmyRefined
  have horiginal :=
    ons_evenHomology_dartEdgeSet_eq_windingParity_of_portEdge_injective
      loop hvalid
      (ons_decCycleDartLoop_portEdge_injective q hq hsnd)
      mx my hmx hmy
  rw [ons_decExpandedKWLoop_edgeSet L q hq] at hrefined
  rw [ons_decCycleDartLoop_edgeSet q hq hsnd] at horiginal
  exact hrefined.trans horiginal.symm

theorem ons_decExpanded_turnProduct_eq_neg_one_of_zero_winding
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hx : ∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2 = 0)
    (hy : ∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2 = 0) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∏ k, ons_turnW ons_turnRoot
        (ons_decExpandedKWLoop L q hq (k + 1)).2
        (ons_decExpandedKWLoop L q hq k).2 = -1 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hroot : ons_turnRoot ≠ 0 := by
    intro h
    have hs := ons_turnRoot_sq
    rw [h] at hs
    have hs' : (0 : ℂ) = Complex.I := by simpa using hs
    exact Complex.I_ne_zero hs'.symm
  apply ons_contractible_turnProduct_eq_neg_one
    ons_turnRoot hroot ons_turnRoot_sq (ons_decExpandedKWLoop L q hq)
    (ons_decExpandedKWLoop_valid L q hq)
    (ons_decExpandedKWLoop_site_injective L q hq)
    (ons_decExpandedKWLoop_nonUturn L q hq) hx hy
  rw [ons_decExpandedDartList_length]
  have := hq.three_le_length
  omega

end StatMech.Onsager
