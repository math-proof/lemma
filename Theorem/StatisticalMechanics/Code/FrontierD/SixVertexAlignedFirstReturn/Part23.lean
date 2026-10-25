/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part25
open StatMech.FrontierD


namespace StatMech.FrontierD

theorem flatten_alignedPermOrderedAllOrbitLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedAllOrbitLists sigma).flatten =
      alignedPermOrderedAllOrbits sigma := by
  rw [alignedPermOrderedAllOrbitLists, List.flatten_append,
    flatten_alignedPermOrderedCycleFactorLists]
  have hsingle (items : List D) :
      (items.map fun d => [d]).flatten = items := by
    induction items with
    | nil => rfl
    | cons d items ih => simp [ih]
  rw [hsingle]
  rfl

theorem alignedPermOrderedAllOrbitLists_chunk_ne_nil
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
    chunk ≠ [] := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · exact alignedPermOrderedCycleFactorLists_chunk_ne_nil
      sigma chunk hfactor
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfixed
    simp

theorem alignedPermOrderedAllOrbitLists_getElem_succ
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (k : Nat) (hk : k + 1 < chunk.length) :
    sigma chunk[k] = chunk[k + 1] := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · rw [alignedPermOrderedCycleFactorLists] at hfactor
    obtain ⟨cycle, hcycleList, rfl⟩ := List.mem_map.mp hfactor
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    simp only [dif_pos hcycle] at hk ⊢
    exact permOrderedCycleFactor_getElem_succ sigma cycle hcycle k hk
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfixed
    simp at hk

theorem alignedPermOrderedAllOrbitLists_getLast
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hnonempty : chunk ≠ []) :
    sigma (chunk.getLast hnonempty) = chunk.head hnonempty := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · rw [alignedPermOrderedCycleFactorLists] at hfactor
    obtain ⟨cycle, hcycleList, rfl⟩ := List.mem_map.mp hfactor
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    simp only [dif_pos hcycle] at hnonempty ⊢
    exact permOrderedCycleFactor_getElem_last sigma cycle hcycle
      hnonempty
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfixed
    change sigma d = d
    simpa [alignedPermOrderedFixedPoints] using hd

theorem alignedPermOrderedAllOrbitLists_mem_forward
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (x : D) (hx : x ∈ chunk) :
    sigma x ∈ chunk := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  by_cases hsucc : k + 1 < chunk.length
  · rw [← hget,
      alignedPermOrderedAllOrbitLists_getElem_succ
        sigma chunk hchunk k hsucc]
    exact List.getElem_mem hsucc
  · have hne : chunk ≠ [] :=
      alignedPermOrderedAllOrbitLists_chunk_ne_nil sigma chunk hchunk
    have hkLast : k = chunk.length - 1 := by omega
    have hxLast : chunk.getLast hne = x := by
      rw [List.getLast_eq_getElem]
      subst k
      exact hget
    rw [← hxLast,
      alignedPermOrderedAllOrbitLists_getLast sigma chunk hchunk hne]
    exact List.head_mem hne

theorem alignedPermOrderedAllOrbitLists_mem_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (x : D) :
    sigma x ∈ chunk ↔ x ∈ chunk := by
  constructor
  · intro hsx
    have hpow : forall k : Nat, (sigma ^ k) (sigma x) ∈ chunk := by
      intro k
      induction k with
      | zero => simpa using hsx
      | succ k ih =>
          rw [pow_succ']
          exact alignedPermOrderedAllOrbitLists_mem_forward
            sigma chunk hchunk _ ih
    have hlast := hpow (orderOf sigma - 1)
    have heq : (sigma ^ (orderOf sigma - 1)) (sigma x) = x := by
      calc
        (sigma ^ (orderOf sigma - 1)) (sigma x) =
            (sigma ^ ((orderOf sigma - 1) + 1)) x := by
          rw [pow_succ]
          rfl
        _ = (sigma ^ orderOf sigma) x := by
          rw [show orderOf sigma - 1 + 1 = orderOf sigma by
            have := orderOf_pos sigma
            omega]
        _ = x := by rw [pow_orderOf_eq_one]; rfl
    rwa [heq] at hlast
  · exact alignedPermOrderedAllOrbitLists_mem_forward
      sigma chunk hchunk x

theorem alignedPermOrderedOrbitChunk_left_forward_of_ne_last
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ [])
    (x : D) (hx : x ∈ left)
    (hne : x ≠ left.getLast hleft) :
    sigma x ∈ left := by
  subst chunk
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  have hkNext : k + 1 < left.length := by
    by_contra hnot
    have hkLast : k = left.length - 1 := by omega
    apply hne
    rw [List.getLast_eq_getElem]
    subst k
    exact hget.symm
  have hsucc := alignedPermOrderedAllOrbitLists_getElem_succ
    sigma (left ++ right) hchunk k (by simp; omega)
  rw [List.getElem_append_left hk,
    List.getElem_append_left hkNext] at hsucc
  rw [← hget, hsucc]
  exact List.getElem_mem hkNext

theorem alignedPermOrderedOrbitChunk_right_forward_of_ne_last
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hright : right ≠ [])
    (x : D) (hx : x ∈ right)
    (hne : x ≠ right.getLast hright) :
    sigma x ∈ right := by
  subst chunk
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  have hkNext : k + 1 < right.length := by
    by_contra hnot
    have hkLast : k = right.length - 1 := by omega
    apply hne
    rw [List.getLast_eq_getElem]
    subst k
    exact hget.symm
  have hsucc := alignedPermOrderedAllOrbitLists_getElem_succ
    sigma (left ++ right) hchunk (left.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega),
    List.getElem_append_right (by omega)] at hsucc
  have hsucc' : sigma right[k] = right[k + 1] := by
    calc
      sigma right[k] =
          sigma right[left.length + k - left.length] := by
        congr 1
        exact getElem_congr rfl (by omega) _
      _ = right[left.length + k + 1 - left.length] := hsucc
      _ = right[k + 1] := getElem_congr rfl (by omega) _
  rw [← hget, hsucc']
  exact List.getElem_mem hkNext

theorem alignedPermOrderedOrbitChunk_split_boundary
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ []) :
    sigma (left.getLast hleft) = right.head hright := by
  subst chunk
  have hleftPos : 0 < left.length := List.length_pos_of_ne_nil hleft
  have hrightPos : 0 < right.length := List.length_pos_of_ne_nil hright
  have hsucc := alignedPermOrderedAllOrbitLists_getElem_succ
    sigma (left ++ right) hchunk (left.length - 1) (by simp; omega)
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  rw [List.getElem_append_left (by omega)] at hsucc
  rw [List.getElem_append_right (by omega)] at hsucc
  calc
    sigma left[left.length - 1] =
        right[left.length - 1 + 1 - left.length] := hsucc
    _ = right[0] := getElem_congr rfl (by omega) _

theorem alignedPermOrderedOrbitChunk_split_entry_boundary
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ []) :
    sigma (right.getLast hright) = left.head hleft := by
  have hne : chunk ≠ [] := by
    rw [hsplit]
    exact List.append_ne_nil_of_left_ne_nil hleft right
  have hcycle := alignedPermOrderedAllOrbitLists_getLast
    sigma chunk hchunk hne
  have hlast : chunk.getLast hne = right.getLast hright := by
    have happ : left ++ right ≠ [] :=
      List.append_ne_nil_of_right_ne_nil left hright
    exact (List.getLast_congr hne happ hsplit).trans
      (List.getLast_append_of_right_ne_nil left right hright)
  have hhead : chunk.head hne = left.head hleft := by
    have happ : left ++ right ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hleft right
    have hcongr : chunk.head hne = (left ++ right).head happ := by
      rw [List.head_eq_getElem, List.head_eq_getElem]
      exact getElem_congr hsplit rfl _
    exact hcongr.trans (List.head_append_of_ne_nil hleft)
  rwa [hlast, hhead] at hcycle

theorem exists_aligned_orbit_chunk_cut
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (left right : List D)
    (hsplit : alignedPermOrderedAllOrbits sigma = left ++ right)
    (hne : alignedPermOrderedAllOrbits sigma ≠ []) :
    exists before cut after cutLeft cutRight,
      alignedPermOrderedAllOrbitLists sigma = before ++ cut :: after /\
        cut = cutLeft ++ cutRight /\
        left = before.flatten ++ cutLeft /\
        right = cutRight ++ after.flatten := by
  have hflatten := flatten_alignedPermOrderedAllOrbitLists sigma
  have hchunks : alignedPermOrderedAllOrbitLists sigma ≠ [] := by
    intro hnil
    rw [hnil] at hflatten
    simp at hflatten
    exact hne hflatten
  apply exists_aligned_chunk_split_of_flatten_eq_append
    (alignedPermOrderedAllOrbitLists sigma) hchunks
    (alignedPermOrderedAllOrbitLists_chunk_ne_nil sigma) left right
  rw [hflatten]
  exact hsplit

set_option maxHeartbeats 800000 in

theorem sum_map_permOrderedAllCycles_eq_support_aligned
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (f : D -> Int) :
    ((permOrderedAllCycles sigma).map f).sum =
      ∑ d ∈ sigma.support, f d := by
  classical
  unfold permOrderedAllCycles
  rw [sum_map_list_flatMap, sum_map_finset_toList]
  have hone : (∑ cycle ∈ sigma.cycleFactorsFinset,
      ((if hcycle : cycle ∈ sigma.cycleFactorsFinset then
          permOrderedCycleFactor sigma cycle hcycle else []).map f).sum) =
      ∑ cycle ∈ sigma.cycleFactorsFinset,
        ∑ d ∈ cycle.support, f d := by
    apply Finset.sum_congr rfl
    intro cycle hcycle
    rw [dif_pos hcycle, sum_map_permOrderedCycleFactor]
  rw [hone]
  have hdisjoint :
      (↑sigma.cycleFactorsFinset : Set (Equiv.Perm D)).PairwiseDisjoint
        (fun cycle => cycle.support) := by
    intro c hc d hd hcd
    exact (sigma.cycleFactorsFinset_pairwise_disjoint
      hc hd hcd).disjoint_support
  have hunion : sigma.cycleFactorsFinset.biUnion
      (fun cycle => cycle.support) = sigma.support := by
    ext d
    rw [Finset.mem_biUnion]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.symm
  rw [<- Finset.sum_biUnion hdisjoint, hunion]

theorem sum_map_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (f : D -> Int) :
    ((alignedPermOrderedAllOrbits sigma).map f).sum = ∑ d, f d := by
  classical
  rw [alignedPermOrderedAllOrbits, List.map_append, List.sum_append,
    sum_map_permOrderedAllCycles_eq_support_aligned]
  unfold alignedPermOrderedFixedPoints
  rw [sum_map_finset_toList]
  let fixed : Finset D := Finset.univ.filter fun d => sigma d = d
  have hdisjoint : Disjoint sigma.support fixed := by
    rw [Finset.disjoint_left]
    intro d hsupport hfixed
    have hne := Equiv.Perm.mem_support.mp hsupport
    have heq : sigma d = d := by simpa [fixed] using hfixed
    exact hne heq
  have hunion : sigma.support ∪ fixed = Finset.univ := by
    ext d
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases h : sigma d = d
    · exact Or.inr (by simp [fixed, h])
    · exact Or.inl (Equiv.Perm.mem_support.mpr h)
  change (∑ d ∈ sigma.support, f d) + ∑ d ∈ fixed, f d = _
  rw [<- Finset.sum_union hdisjoint, hunion]

theorem mem_permOrderedCycleFactor_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset) (d : D) :
    d ∈ permOrderedCycleFactor sigma cycle hcycle ↔
      d ∈ cycle.support := by
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  let enumerate := permCycleFinEquivSupport cycle hc seed
  rw [show permOrderedCycleFactor sigma cycle hcycle =
      List.ofFn (fun k => (enumerate k).1) by rfl]
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    rw [← hi]
    exact (enumerate i).2
  · intro hd
    obtain ⟨i, hi⟩ := enumerate.surjective ⟨d, hd⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem mem_permOrderedAllCycles_iff_support
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (d : D) :
    d ∈ permOrderedAllCycles sigma ↔ d ∈ sigma.support := by
  classical
  rw [permOrderedAllCycles, List.mem_flatMap]
  constructor
  · rintro ⟨cycle, hcycleList, hd⟩
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    rw [dif_pos hcycle,
      mem_permOrderedCycleFactor_iff sigma cycle hcycle d] at hd
    exact
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mpr
        ⟨cycle, hcycle, hd⟩
  · intro hd
    obtain ⟨cycle, hcycle, hdcycle⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hd
    refine ⟨cycle, by simpa, ?_⟩
    rw [dif_pos hcycle,
      mem_permOrderedCycleFactor_iff sigma cycle hcycle d]
    exact hdcycle

theorem mem_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (d : D) :
    d ∈ alignedPermOrderedAllOrbits sigma := by
  classical
  rw [alignedPermOrderedAllOrbits, List.mem_append]
  by_cases hfixed : sigma d = d
  · right
    simp [alignedPermOrderedFixedPoints, hfixed]
  · left
    rw [mem_permOrderedAllCycles_iff_support]
    exact Equiv.Perm.mem_support.mpr hfixed

theorem length_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedAllOrbits sigma).length = Fintype.card D := by
  have hsum := sum_map_alignedPermOrderedAllOrbits sigma
    (Function.const D (1 : Int))
  have hone (items : List D) :
      (items.map (Function.const D (1 : Int))).sum =
        (items.length : Int) := by
    induction items with
    | nil => simp
    | cons d items ih =>
        simp only [List.map_cons, List.sum_cons, Function.const_apply,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [ih]
        omega
  rw [hone] at hsum
  have hsum' : ((alignedPermOrderedAllOrbits sigma).length : Int) =
      (Fintype.card D : Int) := by
    simpa using hsum
  exact Int.ofNat_inj.mp hsum'

theorem alignedPermOrderedAllOrbits_nodup
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedAllOrbits sigma).Nodup := by
  classical
  change ((↑(alignedPermOrderedAllOrbits sigma) : Multiset D)).Nodup
  rw [← Multiset.dedup_card_eq_card_iff_nodup]
  change (alignedPermOrderedAllOrbits sigma).toFinset.card =
    (alignedPermOrderedAllOrbits sigma).length
  rw [show (alignedPermOrderedAllOrbits sigma).toFinset = Finset.univ by
    ext d
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact mem_alignedPermOrderedAllOrbits sigma d]
  simp [length_alignedPermOrderedAllOrbits]

theorem alignedPermOrderedAllOrbitLists_chunk_nodup
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
    chunk.Nodup := by
  have hall : (alignedPermOrderedAllOrbitLists sigma).flatten.Nodup := by
    rw [flatten_alignedPermOrderedAllOrbitLists]
    exact alignedPermOrderedAllOrbits_nodup sigma
  exact (List.nodup_flatten.mp hall).1 chunk hchunk


theorem alignedPermOrderedAllOrbitLists_sameCycle_of_mem
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    {x y : D} (hx : x ∈ chunk) (hy : y ∈ chunk) :
    sigma.SameCycle x y := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · rw [alignedPermOrderedCycleFactorLists] at hfactor
    obtain ⟨cycle, hcycleList, hchunk⟩ := List.mem_map.mp hfactor
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    subst chunk
    simp only [dif_pos hcycle] at hx hy
    have hxSupport :=
      (mem_permOrderedCycleFactor_iff sigma cycle hcycle x).mp hx
    have hySupport :=
      (mem_permOrderedCycleFactor_iff sigma cycle hcycle y).mp hy
    exact (Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset
      hcycle).2 hxSupport hySupport
  · obtain ⟨d, hd, hchunk⟩ := List.mem_map.mp hfixed
    subst chunk
    simp only [List.mem_singleton] at hx hy
    exact (hx.trans hy.symm).sameCycle sigma


theorem alignedPermOrderedAllOrbitLists_prefix_mem_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (parts suffix : List (List D))
    (hall : alignedPermOrderedAllOrbitLists sigma = parts ++ suffix)
    (x : D) :
    sigma x ∈ parts.flatten <-> x ∈ parts.flatten := by
  constructor
  · rw [List.mem_flatten, List.mem_flatten]
    rintro ⟨part, hpart, hsigma⟩
    refine ⟨part, hpart, ?_⟩
    apply (alignedPermOrderedAllOrbitLists_mem_iff sigma part ?_ x).mp hsigma
    rw [hall]
    simp [hpart]
  · rw [List.mem_flatten, List.mem_flatten]
    rintro ⟨part, hpart, hx⟩
    refine ⟨part, hpart, ?_⟩
    apply (alignedPermOrderedAllOrbitLists_mem_iff sigma part ?_ x).mpr hx
    rw [hall]
    simp [hpart]

theorem alignedPermOrderedOrbitChunk_mem_left_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ [])
    (x : D) :
    sigma x ∈ left ↔
      (x ∈ left ∧ x ≠ left.getLast hleft) ∨
        x = right.getLast hright := by
  have hchunkNodup :=
    alignedPermOrderedAllOrbitLists_chunk_nodup sigma chunk hchunk
  have happNodup : (left ++ right).Nodup := by
    simpa [hsplit] using hchunkNodup
  have hdisjoint := (List.nodup_append.mp happNodup).2.2
  constructor
  · intro hsx
    have hsChunk : sigma x ∈ chunk := by
      rw [hsplit, List.mem_append]
      exact Or.inl hsx
    have hxChunk :=
      (alignedPermOrderedAllOrbitLists_mem_iff
        sigma chunk hchunk x).mp hsChunk
    rw [hsplit, List.mem_append] at hxChunk
    rcases hxChunk with hxLeft | hxRight
    · by_cases hxLast : x = left.getLast hleft
      · have hboundary := alignedPermOrderedOrbitChunk_split_boundary
          sigma chunk left right hchunk hsplit hleft hright
        have heq : sigma x = right.head hright := by
          simpa [hxLast] using hboundary
        have hneq := hdisjoint (sigma x) hsx
          (right.head hright) (List.head_mem hright)
        exact False.elim (hneq heq)
      · exact Or.inl ⟨hxLeft, hxLast⟩
    · by_cases hxLast : x = right.getLast hright
      · exact Or.inr hxLast
      · have hsRight :=
          alignedPermOrderedOrbitChunk_right_forward_of_ne_last
            sigma chunk left right hchunk hsplit hright
            x hxRight hxLast
        have hneq := hdisjoint (sigma x) hsx (sigma x) hsRight
        exact False.elim (hneq rfl)
  · rintro (⟨hxLeft, hxLast⟩ | rfl)
    · exact alignedPermOrderedOrbitChunk_left_forward_of_ne_last
        sigma chunk left right hchunk hsplit hleft
        x hxLeft hxLast
    · rw [alignedPermOrderedOrbitChunk_split_entry_boundary
        sigma chunk left right hchunk hsplit hleft hright]
      exact List.head_mem hleft

theorem alignedPermOrderedOrbitPrefix_mem_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D)
    (before : List (List D)) (chunk : List D) (after : List (List D))
    (left right : List D)
    (hall : alignedPermOrderedAllOrbitLists sigma =
      before ++ chunk :: after)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ [])
    (x : D) :
    sigma x ∈ before.flatten ++ left ↔
      (x ∈ before.flatten ++ left ∧ x ≠ left.getLast hleft) ∨
        x = right.getLast hright := by
  have hbefore (y : D) :
      sigma y ∈ before.flatten ↔ y ∈ before.flatten := by
    constructor
    · rw [List.mem_flatten, List.mem_flatten]
      rintro ⟨part, hpart, hsigma⟩
      refine ⟨part, hpart, ?_⟩
      apply (alignedPermOrderedAllOrbitLists_mem_iff
        sigma part ?_ y).mp hsigma
      rw [hall]
      simp [hpart]
    · rw [List.mem_flatten, List.mem_flatten]
      rintro ⟨part, hpart, hy⟩
      refine ⟨part, hpart, ?_⟩
      apply (alignedPermOrderedAllOrbitLists_mem_iff
        sigma part ?_ y).mpr hy
      rw [hall]
      simp [hpart]
  have hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma := by
    rw [hall]
    simp
  have hflatNodup :
      (alignedPermOrderedAllOrbitLists sigma).flatten.Nodup := by
    rw [flatten_alignedPermOrderedAllOrbitLists]
    exact alignedPermOrderedAllOrbits_nodup sigma
  have hprefixNodup : (before.flatten ++ chunk).Nodup := by
    rw [hall, List.flatten_append, List.flatten_cons] at hflatNodup
    have hreassoc :
        ((before.flatten ++ chunk) ++ after.flatten).Nodup := by
      simpa [List.append_assoc] using hflatNodup
    exact hreassoc.of_append_left
  have hdisjoint : before.flatten.Disjoint chunk := by
    rw [List.disjoint_left]
    intro a ha hac
    exact (List.nodup_append.mp hprefixNodup).2.2 a ha a hac rfl
  rw [List.mem_append, List.mem_append]
  constructor
  · rintro (hsBefore | hsLeft)
    · have hxBefore := (hbefore x).mp hsBefore
      refine Or.inl ⟨Or.inl hxBefore, ?_⟩
      intro hxLast
      apply hdisjoint hxBefore
      rw [hsplit, List.mem_append]
      exact Or.inl (hxLast ▸ List.getLast_mem hleft)
    · rcases (alignedPermOrderedOrbitChunk_mem_left_iff
          sigma chunk left right hchunk hsplit hleft hright x).mp hsLeft with
        ⟨hxLeft, hxLast⟩ | hxEntry
      · exact Or.inl ⟨Or.inr hxLeft, hxLast⟩
      · exact Or.inr hxEntry
  · rintro (⟨hxSelected, hxLast⟩ | hxEntry)
    · rcases hxSelected with hxBefore | hxLeft
      · exact Or.inl ((hbefore x).mpr hxBefore)
      · exact Or.inr
          ((alignedPermOrderedOrbitChunk_mem_left_iff
            sigma chunk left right hchunk hsplit hleft hright x).mpr
              (Or.inl ⟨hxLeft, hxLast⟩))
    · exact Or.inr
        ((alignedPermOrderedOrbitChunk_mem_left_iff
          sigma chunk left right hchunk hsplit hleft hright x).mpr
            (Or.inr hxEntry))

theorem exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned
    {A : Type*} (items : List A) (step : A -> Int)
    (hsteps : forall x, x ∈ items ->
      step x = 0 \/ step x = 1 \/ step x = -1)
    (target total : Int) (hsum : (items.map step).sum = total)
    (htarget_nonneg : 0 <= target) (htarget_le : target <= total) :
    exists pre suf : List A,
      items = pre ++ suf /\ (pre.map step).sum = target := by
  induction items generalizing target total with
  | nil =>
      have htarget : target = 0 := by
        simp only [List.map_nil, List.sum_nil] at hsum
        omega
      exact ⟨[], [], rfl, by simp [htarget]⟩
  | cons x items ih =>
      have hx := hsteps x (by simp)
      have htail : forall y, y ∈ items ->
          step y = 0 \/ step y = 1 \/ step y = -1 := by
        intro y hy
        exact hsteps y (by simp [hy])
      by_cases htarget : target = 0
      · exact ⟨[], x :: items, by simp, by simp [htarget]⟩
      · have htarget_pos : 0 < target := by omega
        rcases hx with hx | hx | hx
        · have htailSum : (items.map step).sum = total := by
            simp only [List.map_cons, List.sum_cons, hx, zero_add] at *
            assumption
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            ih htail target total htailSum htarget_nonneg htarget_le
          exact ⟨x :: pre, suf, by simp [hsplit], by simp [hx, hprefix]⟩
        · have htailSum : (items.map step).sum = total - 1 := by
            simp only [List.map_cons, List.sum_cons, hx] at *
            omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ := ih htail
            (target - 1) (total - 1) htailSum (by omega) (by omega)
          exact ⟨x :: pre, suf, by simp [hsplit], by simp [hx, hprefix]⟩
        · have htailSum : (items.map step).sum = total + 1 := by
            simp only [List.map_cons, List.sum_cons, hx] at *
            omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ := ih htail
            (target + 1) (total + 1) htailSum (by omega) (by omega)
          exact ⟨x :: pre, suf, by simp [hsplit], by simp [hx, hprefix]⟩

theorem exists_two_unit_blocks_of_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (step : D -> Int)
    (hsteps : forall d, step d = 0 \/ step d = 1 \/ step d = -1)
    (hsum : ∑ d, step d = 2) :
    exists first second : List D,
      alignedPermOrderedAllOrbits sigma = first ++ second /\
        (first.map step).sum = 1 /\
        (second.map step).sum = 1 := by
  obtain ⟨first, second, hsplit, hfirst⟩ :=
    exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned
      (alignedPermOrderedAllOrbits sigma) step (fun d hd => hsteps d)
      1 2 (by rw [sum_map_alignedPermOrderedAllOrbits]; exact hsum)
      (by norm_num) (by norm_num)
  refine ⟨first, second, hsplit, hfirst, ?_⟩
  have htotal : ((alignedPermOrderedAllOrbits sigma).map step).sum = 2 := by
    rw [sum_map_alignedPermOrderedAllOrbits]
    exact hsum
  rw [hsplit, List.map_append, List.sum_append, hfirst] at htotal
  omega

end StatMech.FrontierD
