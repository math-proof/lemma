/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part9


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSPairIndex_ne_reflect {T L : ℕ} (i : HexCSPairIndex T L) :
    i.1 ≠ hexCSReflectIncidence i.1 := by
  intro h
  exact (Nat.ne_of_lt i.2.2) (congrArg hexCSIncidenceRank h)

theorem hexCSStartIncidence_reflect (T L : ℕ) (hT : 0 < T) :
    hexCSReflectIncidence (hexCSStartIncidence T L hT) =
      hexCSStartIncidence T L hT := by
  rw [hexCSReflectIncidence, hexCSStartIncidence, HexIncidence.mk.injEq]
  exact ⟨by apply Subtype.ext; rfl, rfl⟩


theorem hexCS_mem_orbit_biUnion_iff {T L : ℕ} (hT : 0 < T)
    (e : HexCSIncidence T L) :
    e ∈ Finset.univ.biUnion
        (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) ↔
      e ∈ hexCSBoundaryIncidences T L ∧
        e ≠ hexCSStartIncidence T L hT := by
  constructor
  · intro he
    rw [Finset.mem_biUnion] at he
    obtain ⟨o, _, heo⟩ := he
    cases o with
    | inl i =>
        simp only [hexCSOrbitPiece, hexCSPairPiece,
          Finset.mem_insert, Finset.mem_singleton] at heo
        rcases heo with rfl | rfl
        · refine ⟨i.2.1, ?_⟩
          intro hs
          apply hexCSPairIndex_ne_reflect i
          calc
            i.1 = hexCSStartIncidence T L hT := hs
            _ = hexCSReflectIncidence (hexCSStartIncidence T L hT) :=
              (hexCSStartIncidence_reflect T L hT).symm
            _ = hexCSReflectIncidence i.1 :=
              congrArg hexCSReflectIncidence hs.symm
        · refine ⟨(hexCSReflectIncidence_mem_boundary_iff i.1).2 i.2.1, ?_⟩
          intro hs
          apply hexCSPairIndex_ne_reflect i
          calc
            i.1 = hexCSReflectIncidence (hexCSReflectIncidence i.1) :=
              (hexCSReflectIncidence_invol i.1).symm
            _ = hexCSReflectIncidence (hexCSStartIncidence T L hT) :=
              congrArg hexCSReflectIncidence hs
            _ = hexCSStartIncidence T L hT :=
              hexCSStartIncidence_reflect T L hT
            _ = hexCSReflectIncidence i.1 := hs.symm
    | inr k =>
        have heq : e = k.1 := by simpa [hexCSOrbitPiece, hexCSFixedPiece] using heo
        subst e
        exact ⟨k.2.1, k.2.2.2⟩
  · rintro ⟨heBoundary, heStart⟩
    by_cases hfixed : hexCSReflectIncidence e = e
    · rw [Finset.mem_biUnion]
      let k : HexCSFixedIndex T L hT := ⟨e, heBoundary, hfixed, heStart⟩
      exact ⟨Sum.inr k, Finset.mem_univ _, by
        simp [hexCSOrbitPiece, hexCSFixedPiece, k]⟩
    · have hrank :
          hexCSIncidenceRank e < hexCSIncidenceRank (hexCSReflectIncidence e) ∨
          hexCSIncidenceRank (hexCSReflectIncidence e) < hexCSIncidenceRank e := by
        rcases lt_trichotomy (hexCSIncidenceRank e)
            (hexCSIncidenceRank (hexCSReflectIncidence e)) with h | h | h
        · exact Or.inl h
        · exact False.elim (hfixed (hexCSIncidenceRank_injective h.symm))
        · exact Or.inr h
      rw [Finset.mem_biUnion]
      cases hrank with
      | inl hlt =>
          let i : HexCSPairIndex T L := ⟨e, heBoundary, hlt⟩
          exact ⟨Sum.inl i, Finset.mem_univ _, by
            simp [hexCSOrbitPiece, hexCSPairPiece, i]⟩
      | inr hlt =>
          let er := hexCSReflectIncidence e
          have herBoundary : er ∈ hexCSBoundaryIncidences T L :=
            (hexCSReflectIncidence_mem_boundary_iff e).2 heBoundary
          have herlt : hexCSIncidenceRank er <
              hexCSIncidenceRank (hexCSReflectIncidence er) := by
            simpa [er] using hlt
          let i : HexCSPairIndex T L := ⟨er, herBoundary, herlt⟩
          exact ⟨Sum.inl i, Finset.mem_univ _, by
            simp [hexCSOrbitPiece, hexCSPairPiece, i, er]⟩

theorem hexCS_boundary_orbit_partition (T L : ℕ) (hT : 0 < T) :
    hexCSBoundaryIncidences T L =
      {hexCSStartIncidence T L hT} ∪
        Finset.univ.biUnion
          (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
  ext e
  rw [Finset.mem_union, Finset.mem_singleton,
    hexCS_mem_orbit_biUnion_iff]
  constructor
  · intro he
    by_cases hs : e = hexCSStartIncidence T L hT
    · exact Or.inl hs
    · exact Or.inr ⟨he, hs⟩
  · rintro (rfl | ⟨he, _⟩)
    · exact hexCSStartIncidence_mem_boundary T L hT
    · exact he

theorem hexCS_start_orbits_disjoint (T L : ℕ) (hT : 0 < T) :
    Disjoint ({hexCSStartIncidence T L hT} : Finset (HexCSIncidence T L))
      (Finset.univ.biUnion
        (hexCSOrbitPiece (T := T) (L := L) (hT := hT))) := by
  rw [Finset.disjoint_left]
  intro e heStart heOrbit
  have hs : e = hexCSStartIncidence T L hT := by simpa using heStart
  exact (hexCS_mem_orbit_biUnion_iff hT e).1 heOrbit |>.2 hs

theorem hexCS_pairPieces_disjoint {T L : ℕ}
    (i j : HexCSPairIndex T L) (hij : i ≠ j) :
    Disjoint (hexCSPairPiece i) (hexCSPairPiece j) := by
  rw [Finset.disjoint_left]
  intro e hei hej
  simp only [hexCSPairPiece, Finset.mem_insert, Finset.mem_singleton] at hei hej
  rcases hei with hi | hi <;> rcases hej with hj | hj
  · apply hij; apply Subtype.ext; exact hi.symm.trans hj
  · have hcross : i.1 = hexCSReflectIncidence j.1 := hi.symm.trans hj
    have hcross' : hexCSReflectIncidence i.1 = j.1 := by
      have := congrArg hexCSReflectIncidence hcross
      simpa using this
    have hlt := i.2.2
    rw [hcross'] at hlt
    have hgt := j.2.2
    rw [← hcross] at hgt
    omega
  · have hcross : hexCSReflectIncidence i.1 = j.1 := hi.symm.trans hj
    have hcross' : i.1 = hexCSReflectIncidence j.1 := by
      have := congrArg hexCSReflectIncidence hcross
      simpa using this
    have hlt := j.2.2
    rw [← hcross'] at hlt
    have hgt := i.2.2
    rw [hcross] at hgt
    omega
  · apply hij; apply Subtype.ext
    have hreflect : hexCSReflectIncidence i.1 =
        hexCSReflectIncidence j.1 := hi.symm.trans hj
    have := congrArg hexCSReflectIncidence hreflect
    simpa using this

theorem hexCS_pair_fixed_disjoint {T L : ℕ} {hT : 0 < T}
    (i : HexCSPairIndex T L) (k : HexCSFixedIndex T L hT) :
    Disjoint (hexCSPairPiece i) (hexCSFixedPiece k) := by
  rw [Finset.disjoint_left]
  intro e hei hek
  have heq : e = k.1 := by simpa [hexCSFixedPiece] using hek
  subst e
  simp only [hexCSPairPiece, Finset.mem_insert, Finset.mem_singleton] at hei
  rcases hei with hi | hi
  · apply hexCSPairIndex_ne_reflect i
    calc
      i.1 = k.1 := hi.symm
      _ = hexCSReflectIncidence k.1 := k.2.2.1.symm
      _ = hexCSReflectIncidence i.1 := congrArg hexCSReflectIncidence hi
  · apply hexCSPairIndex_ne_reflect i
    calc
      i.1 = hexCSReflectIncidence (hexCSReflectIncidence i.1) :=
        (hexCSReflectIncidence_invol i.1).symm
      _ = hexCSReflectIncidence k.1 := congrArg hexCSReflectIncidence hi.symm
      _ = k.1 := k.2.2.1
      _ = hexCSReflectIncidence i.1 := hi

theorem hexCS_fixedPieces_disjoint {T L : ℕ} {hT : 0 < T}
    (k l : HexCSFixedIndex T L hT) (hkl : k ≠ l) :
    Disjoint (hexCSFixedPiece k) (hexCSFixedPiece l) := by
  rw [Finset.disjoint_left]
  intro e hek hel
  apply hkl
  apply Subtype.ext
  have hk : e = k.1 := by simpa [hexCSFixedPiece] using hek
  have hl : e = l.1 := by simpa [hexCSFixedPiece] using hel
  exact hk.symm.trans hl

theorem hexCS_orbitPieces_pairwiseDisjoint (T L : ℕ) (hT : 0 < T) :
    ((Finset.univ : Finset
      (HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT)) :
        Set (HexCSPairIndex T L ⊕ HexCSFixedIndex T L hT)).PairwiseDisjoint
      (hexCSOrbitPiece (T := T) (L := L) (hT := hT)) := by
  intro o _ p _ hop
  cases o with
  | inl i =>
      cases p with
      | inl j =>
          exact hexCS_pairPieces_disjoint i j
            (fun hij => hop (congrArg Sum.inl hij))
      | inr k =>
          exact hexCS_pair_fixed_disjoint i k
  | inr k =>
      cases p with
      | inl i =>
          exact (hexCS_pair_fixed_disjoint i k).symm
      | inr l =>
          exact hexCS_fixedPieces_disjoint k l
            (fun hkl => hop (congrArg Sum.inr hkl))


end
end StatMech.Universality
