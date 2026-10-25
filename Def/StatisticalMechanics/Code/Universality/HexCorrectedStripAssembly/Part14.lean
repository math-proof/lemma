/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part12


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSEndpointBoundaryCore
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    HexEndpointBoundaryCore (hexCSFiniteRegion T L hT) 1
      (hexCSDomain T L hT hlocal)
      (hexCSDomainInteriorPairing T L hT hlocal) where
  interior_sub := hexCSDomainInteriorPairing_interior_sub T L hT hlocal
  obs_eq := fun _ => rfl
  start_value := by
    exact endpointParafObservable_start_eq_one_of_unique
      (hexCSFiniteRegion T L hT) 1 hstart


noncomputable def hexCSEndpointMirrorOrbitData
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    HexEndpointMirrorOrbitData
      (I := HexCSPairIndex T L) (K := HexCSFixedIndex T L hT)
      (hexCSEndpointBoundaryCore T L hT hlocal hstart) where
  heading := @hexCSHeading T L
  hgeom := hexCSHeading_geometry
  startIncidence := hexCSStartIncidence T L hT
  start_mid := hexCSStartIncidence_mid T L hT
  start_heading := by
    simp [hexCSHeading, hexCSStartIncidence, hexCSCanonicalHeading,
      hexCSOrigin, hexAWOriginCoord, hexAWTrans]
  pairs := hexCSBoundaryPair T L hT hlocal hlaw
  fixed := hexCSBoundaryFixed T L hT hlocal hlaw
  boundary_partition := by
    rw [hexCSDomain_incidences_eq]
    change hexCSIncidences T L \ hexCSInteriorIncidences T L = _
    simp only [hexCSBoundaryPair_piece T L hT hlocal hlaw,
      hexCSBoundaryFixed_piece T L hT hlocal hlaw]
    ext e
    simp only [Finset.mem_sdiff, hexCS_mem_incidences, true_and,
      hexCS_mem_interior_iff, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro hinterior
      by_cases hs : e = hexCSStartIncidence T L hT
      · exact Or.inl hs
      · right
        have heBoundary : e ∈ hexCSBoundaryIncidences T L :=
          (hexCS_mem_boundary_iff e).2 hinterior
        rw [Finset.mem_biUnion]
        by_cases hfixed : hexCSReflectIncidence e = e
        · let k : HexCSFixedIndex T L hT :=
            ⟨e, heBoundary, hfixed, hs⟩
          exact ⟨Sum.inr k, Finset.mem_univ _, by
            simp [hexCSFixedPiece, k]⟩
        · have hrank :
              hexCSIncidenceRank e <
                  hexCSIncidenceRank (hexCSReflectIncidence e) ∨
                hexCSIncidenceRank (hexCSReflectIncidence e) <
                  hexCSIncidenceRank e := by
            rcases lt_trichotomy (hexCSIncidenceRank e)
                (hexCSIncidenceRank (hexCSReflectIncidence e)) with h | h | h
            · exact Or.inl h
            · exact False.elim
                (hfixed (hexCSIncidenceRank_injective h.symm))
            · exact Or.inr h
          cases hrank with
          | inl hlt =>
              let i : HexCSPairIndex T L := ⟨e, heBoundary, hlt⟩
              exact ⟨Sum.inl i, Finset.mem_univ _, by
                simp [hexCSPairPiece, i]⟩
          | inr hlt =>
              let er := hexCSReflectIncidence e
              have herBoundary : er ∈ hexCSBoundaryIncidences T L :=
                (hexCSReflectIncidence_mem_boundary_iff e).2 heBoundary
              have herlt : hexCSIncidenceRank er <
                  hexCSIncidenceRank (hexCSReflectIncidence er) := by
                simpa [er] using hlt
              let i : HexCSPairIndex T L := ⟨er, herBoundary, herlt⟩
              exact ⟨Sum.inl i, Finset.mem_univ _, by
                simp [hexCSPairPiece, i, er]⟩
    · rintro (rfl | he)
      · exact (hexCS_mem_boundary_iff _).1
          (hexCSStartIncidence_mem_boundary T L hT)
      · rw [Finset.mem_biUnion] at he
        obtain ⟨o, _, heo⟩ := he
        cases o with
        | inl i =>
            simp only [hexCSPairPiece, Finset.mem_insert,
              Finset.mem_singleton] at heo
            rcases heo with rfl | rfl
            · exact (hexCS_mem_boundary_iff _).1 i.2.1
            · exact (hexCS_mem_boundary_iff _).1
                ((hexCSReflectIncidence_mem_boundary_iff i.1).2 i.2.1)
        | inr k =>
            have heq : e = k.1 := by
              simpa [hexCSFixedPiece] using heo
            subst e
            exact (hexCS_mem_boundary_iff _).1 k.2.1
  start_orbits_disjoint := by
    simpa [hexCSBoundaryPair_piece, hexCSBoundaryFixed_piece] using
      (hexCS_start_orbits_disjoint T L hT)
  orbits_disjoint := by
    simp only [hexCSBoundaryPair_piece, hexCSBoundaryFixed_piece]
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

noncomputable def hexCSDCSClassification
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    (hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart).DCSClassification where
  classOf i := hexCSBoundaryClass i.1
  cos_angle := by
    intro i
    simpa [hexCSEndpointMirrorOrbitData, hexCSBoundaryPair,
      endpointMirrorBoundaryPair_of_reflection] using
        (hexCS_boundary_cosine i.1 i.2.1)


end
end StatMech.Universality
