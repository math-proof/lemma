/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part76
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_walkIndexInterval_support
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) (i j : Nat)
    (hi : i ≤ W.length) (hij : i ≤ j) (hj : j ≤ W.length)
    {v : V} (hv : v ∈ (rlc_walkIndexInterval W i j hi hij hj).support) :
    ∃ k : Nat, i ≤ k ∧ k ≤ j ∧ W.getVert k = v := by
  change v ∈ (((W.drop i).take (j - i)).copy _ _).support at hv
  rw [SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨m, hvm, hm⟩ := hv
  have hmBounds : m ≤ j - i ∧ m ≤ W.length - i := by
    simpa using hm
  refine ⟨i + m, by omega, by omega, ?_⟩
  rw [← hvm, SimpleGraph.Walk.take_getVert,
    SimpleGraph.Walk.drop_getVert]
  congr 1
  omega


theorem rlc_walkIndexInterval_getVert_mem
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) (i j : Nat)
    (hi : i ≤ W.length) (hij : i ≤ j) (hj : j ≤ W.length)
    {k : Nat} (hik : i ≤ k) (hkj : k ≤ j) :
    W.getVert k ∈ (rlc_walkIndexInterval W i j hi hij hj).support := by
  let H := rlc_walkIndexInterval W i j hi hij hj
  have hget : H.getVert (k - i) = W.getVert k := by
    dsimp only [H, rlc_walkIndexInterval]
    rw [SimpleGraph.Walk.getVert_copy,
      SimpleGraph.Walk.take_getVert,
      SimpleGraph.Walk.drop_getVert]
    congr 1
    omega
  rw [← hget]
  exact H.getVert_mem_support (k - i)


theorem rlc_walkIndexInterval_support_interior
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) (i j : Nat)
    (hi : i ≤ W.length) (hij : i ≤ j) (hj : j ≤ W.length)
    {v : V} (hv : v ∈ (rlc_walkIndexInterval W i j hi hij hj).support)
    (hvi : v ≠ W.getVert i) (hvj : v ≠ W.getVert j) :
    ∃ k : Nat, i < k ∧ k < j ∧ W.getVert k = v := by
  obtain ⟨k, hik, hkj, hkv⟩ :=
    rlc_walkIndexInterval_support W i j hi hij hj hv
  refine ⟨k, ?_, ?_, hkv⟩
  · exact lt_of_le_of_ne hik (by
      intro hki
      apply hvi
      rw [← hkv, hki])
  · exact lt_of_le_of_ne hkj (by
      intro hkj'
      apply hvj
      rw [← hkv, hkj'])


theorem rlc_walk_ordered_to_complementary_crosscut
    {G K : SimpleGraph (Site 2)}
    {u x y a b : Site 2} (c : G.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (W : K.Walk a b)
    (ha : a ∈ (rlc_orderedContourArc c hx hy).support)
    (hb : b ∈ (rlc_complementaryContourArc c hx hy).support) :
    (∃ z ∈ W.support,
        z ∈ (rlc_orderedContourArc c hx hy).support ∧
          z ∈ (rlc_complementaryContourArc c hx hy).support) ∨
      ∃ (i j : Nat) (hi : i ≤ W.length) (hij : i ≤ j)
          (hj : j ≤ W.length),
        i < j ∧
          W.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧
          W.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧
          ∀ z ∈ (rlc_walkIndexInterval W i j hi hij hj).support,
            z = W.getVert i ∨ z = W.getVert j ∨ z ∉ c.support := by
  rcases rlc_walk_ordered_to_complementary_contact_interval
      c hx hy W ha hb with hcommon | ⟨i, j, hij, hj, hiArc, hjArc, hbetween⟩
  · exact Or.inl hcommon
  · right
    have hi : i ≤ W.length := by omega
    have hij' : i ≤ j := hij.le
    refine ⟨i, j, hi, hij', hj, hij, hiArc, hjArc, ?_⟩
    intro z hz
    by_cases hzi : z = W.getVert i
    · exact Or.inl hzi
    by_cases hzj : z = W.getVert j
    · exact Or.inr (Or.inl hzj)
    · right; right
      obtain ⟨k, hik, hkj, hkz⟩ :=
        rlc_walkIndexInterval_support_interior
          W i j hi hij' hj hz hzi hzj
      rw [← hkz]
      exact hbetween k hik hkj


theorem rlc_walk_exists_first_contact_after
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b u : V} (W : G.Walk a b) (C : G.Walk u u)
    {j : Nat} (hjLength : j < W.length) (hend : b ∈ C.support) :
    ∃ j' : Nat,
      j < j' ∧ j' ≤ W.length ∧ W.getVert j' ∈ C.support ∧
        ∀ l : Nat, j < l → l < j' → W.getVert l ∉ C.support := by
  classical
  let R : Finset Nat := (Finset.Icc (j + 1) W.length).filter fun k =>
    W.getVert k ∈ C.support
  have hlengthR : W.length ∈ R := by
    simp [R, hjLength, W.getVert_length, hend]
  obtain ⟨j', hj'R, hj'Min⟩ :=
    Finset.exists_min_image R id ⟨W.length, hlengthR⟩
  have hj'Info := Finset.mem_filter.mp hj'R
  have hj'Bounds := Finset.mem_Icc.mp hj'Info.1
  refine ⟨j', by omega, hj'Bounds.2, hj'Info.2, ?_⟩
  intro l hjl hlj' hlContact
  have hlR : l ∈ R := Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hlContact⟩
  have hj'l : j' ≤ l := by simpa using hj'Min l hlR
  omega


theorem rlc_walk_contactInterval_same_leftRegion_side
    {a b u : Site 2}
    (W : (hypercubicLattice 2).Walk a b)
    (C : (hypercubicLattice 2).Walk u u)
    {i k j : Nat}
    (hik : i < k) (hkj : k < j) (hjLength : j ≤ W.length)
    (hbetween : ∀ l : Nat, i < l → l < j →
      W.getVert l ∉ C.support)
    (hkOutside : W.getVert k ∉ jec_leftRegion C) :
    ∀ l : Nat, i < l → l < j →
      W.getVert l ∉ jec_leftRegion C := by
  intro l hil hlj
  have hkLength : k ≤ W.length := by omega
  have hlLength : l ≤ W.length := by omega
  rcases le_total l k with hlk | hkl
  · let p := (W.drop l).take (k - l)
    have hpLength : p.length = k - l := by
      simp [p, Nat.min_eq_left]
      omega
    have hpOff : ∀ z ∈ p.support, z ∉ C.support := by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
      obtain ⟨m, hzm, hm⟩ := hz
      have hm' : m ≤ k - l := by simpa [hpLength] using hm
      have hget : p.getVert m = W.getVert (l + m) := by
        simp [p, Nat.min_eq_right hm']
      rw [← hzm, hget]
      apply hbetween (l + m)
      · omega
      · omega
    have hsame := jlri_sameRegion_along_offSupport_walk C p hpOff
    have hend : (W.drop l).getVert (k - l) = W.getVert k := by
      simp
      congr 1
      omega
    rw [hend] at hsame
    exact fun hlInside => hkOutside (hsame.mp hlInside)
  · let p := (W.drop k).take (l - k)
    have hpLength : p.length = l - k := by
      simp [p, Nat.min_eq_left]
      omega
    have hpOff : ∀ z ∈ p.support, z ∉ C.support := by
      intro z hz
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
      obtain ⟨m, hzm, hm⟩ := hz
      have hm' : m ≤ l - k := by simpa [hpLength] using hm
      have hget : p.getVert m = W.getVert (k + m) := by
        simp [p, Nat.min_eq_right hm']
      rw [← hzm, hget]
      apply hbetween (k + m)
      · omega
      · omega
    have hsame := jlri_sameRegion_along_offSupport_walk C p hpOff
    have hend : (W.drop k).getVert (l - k) = W.getVert l := by
      simp
      congr 1
      omega
    rw [hend] at hsame
    exact fun hlInside => hkOutside (hsame.mpr hlInside)


theorem rlc_walk_ordered_to_complementary_contactInterval_exteriorSide
    {G : SimpleGraph (Site 2)}
    (hG : G ≤ hypercubicLattice 2)
    {u x y a b : Site 2} (c : G.Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (W : (hypercubicLattice 2).Walk a b)
    (ha : a ∈ (rlc_orderedContourArc c hx hy).support)
    (hb : b ∈ (rlc_complementaryContourArc c hx hy).support) :
    (∃ z ∈ W.support,
        z ∈ (rlc_orderedContourArc c hx hy).support ∧
          z ∈ (rlc_complementaryContourArc c hx hy).support) ∨
      ∃ i j : Nat,
        i < j ∧ j ≤ W.length ∧
          W.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧
          W.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧
          (∀ l : Nat, i < l → l < j → W.getVert l ∉ c.support) ∧
          (j = i + 1 ∨
            (i + 1 < j ∧
              ∀ (_hfirstOutside : W.getVert (i + 1) ∉
                  jec_leftRegion (c.mapLe hG)) (l : Nat),
                i < l → l < j →
                  W.getVert l ∉ jec_leftRegion (c.mapLe hG))) := by
  rcases rlc_walk_ordered_to_complementary_contact_interval
      c hx hy W ha hb with
    hcommon | ⟨i, j, hij, hjLength, hiArc, hjArc, hbetween⟩
  · exact Or.inl hcommon
  · right
    refine ⟨i, j, hij, hjLength, hiArc, hjArc, hbetween, ?_⟩
    by_cases hadjacent : j = i + 1
    · exact Or.inl hadjacent
    · right
      have hfirst : i < i + 1 := by omega
      have hfirstj : i + 1 < j := by omega
      refine ⟨hfirstj, ?_⟩
      intro hfirstOutside
      apply rlc_walk_contactInterval_same_leftRegion_side
        W (c.mapLe hG) hfirst hfirstj hjLength
      · intro l hil hlj
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using
          hbetween l hil hlj
      · exact hfirstOutside


theorem rlc_contactInterval_firstVertex_exterior_no_go :
    ∃ (c : (hypercubicLattice 2).Walk ![0, 0] ![0, 0])
      (T : (hypercubicLattice 2).Walk ![2, 1] ![0, 1]),
      c.IsCycle ∧
      T.getVert 0 ∈ c.support ∧ T.getVert 2 ∈ c.support ∧
      (∀ l : Nat, 0 < l → l < 2 → T.getVert l ∉ c.support) ∧
      T.getVert 1 ∈ jec_leftRegion c := by
  let s1 : (hypercubicLattice 2).Walk ![0, 0] ![2, 0] :=
    (jec_hsegRight 0 0 2).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)
  let s2 : (hypercubicLattice 2).Walk ![2, 0] ![2, 2] :=
    (jec_vsegUp 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let s3 : (hypercubicLattice 2).Walk ![2, 2] ![0, 2] :=
    ((jec_hsegRight 2 0 2).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)).reverse
  let s4 : (hypercubicLattice 2).Walk ![0, 2] ![0, 0] :=
    ((jec_vsegUp 0 0 2).copy rfl
      (by ext i; fin_cases i <;> simp)).reverse
  let c := s1.append (s2.append (s3.append s4))
  let T : (hypercubicLattice 2).Walk ![2, 1] ![0, 1] :=
    ((jec_hsegRight 1 0 2).copy (by ext i; fin_cases i <;> simp)
      (by ext i; fin_cases i <;> simp)).reverse
  refine ⟨c, T, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [c, s1, s2, s3, s4]
    rw [SimpleGraph.Walk.isCycle_def]
    simp [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_cons,
      jec_hsegRight, jec_vsegUp]
  · dsimp [T, c, s1, s2, s3, s4]
    simp [jec_hsegRight, jec_vsegUp]
  · dsimp [T, c, s1, s2, s3, s4]
    simp [jec_hsegRight, jec_vsegUp]
  · intro l hl0 hl2
    have hl : l = 1 := by omega
    subst l
    dsimp [T, c, s1, s2, s3, s4]
    simp [jec_hsegRight, jec_vsegUp]
  · have hTmid : T.getVert 1 = (![1, 1] : Site 2) := by
      dsimp [T]
      simp [jec_hsegRight]
    rw [hTmid, jec_mem_leftRegion]
    dsimp [T, c, s1, s2, s3, s4]
    classical
    simp [jec_rayCount, jec_rayEdge, jec_hsegRight, jec_vsegUp]


end
end StatMech.Universality
