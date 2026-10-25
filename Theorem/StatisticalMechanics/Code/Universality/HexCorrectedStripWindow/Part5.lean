/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part5


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCS_inside_brick_bounds
    {T L : ℕ} (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    let R : ℤ := hexCSBrickRadius T L
    (-R < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 ∧
      (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 < R ∧
      -R < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 ∧
      (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 < R) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong] at hc
  all_goals
    simp [hexCSBrickRadius, hexBrickPos, hexCSOutsideStartCoord]
    omega


theorem hexCS_periodicCoord_injective_of_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : 0 < dx)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      0 ≤ z.1 ∧ z.1 < dx) :
    Function.Injective
      (ons_periodStateCoord (fun i : Fin l.length => l.get i)) := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hverts : (ons_pathVertices l).dropLast =
      List.ofFn (StatMech.Onsager.BaseCase.pos d) :=
    ons_pathVertices_dropLast_eq_ofFn_pos l
  intro a b hab
  rcases a with ⟨ra, ia⟩
  rcases b with ⟨rb, ib⟩
  have hpaMem : StatMech.Onsager.BaseCase.pos d ia ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ia, rfl⟩
  have hpbMem : StatMech.Onsager.BaseCase.pos d ib ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ib, rfl⟩
  have hxa := hx _ hpaMem
  have hxb := hx _ hpbMem
  have hfirst := congrArg Prod.fst hab
  have hperiodDisp : ons_pathDisplacement (List.ofFn d) = (dx, dy) := by
    rw [List.ofFn_get]
    exact hdisp
  change StatMech.Onsager.BaseCase.pos d ia +
      ra • ons_pathDisplacement (List.ofFn d) =
    StatMech.Onsager.BaseCase.pos d ib +
      rb • ons_pathDisplacement (List.ofFn d) at hab
  have hfirst' := congrArg Prod.fst hab
  rw [hperiodDisp] at hfirst'
  simp only [Prod.fst_add, Prod.smul_mk, nsmul_eq_mul] at hfirst'
  have hra : ra = rb := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (rb : ℤ) * dx - (ra : ℤ) * dx ≥ dx := by
        have : (ra : ℤ) + 1 ≤ rb := by exact_mod_cast hlt
        nlinarith
      nlinarith [hfirst']
    · have : (ra : ℤ) * dx - (rb : ℤ) * dx ≥ dx := by
        have : (rb : ℤ) + 1 ≤ ra := by exact_mod_cast hgt
        nlinarith
      nlinarith [hfirst']
  subst rb
  have hpos : StatMech.Onsager.BaseCase.pos d ia =
      StatMech.Onsager.BaseCase.pos d ib := by
    simpa [ons_periodStateCoord] using hab
  have hget : ia = ib := by
    have hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d) :=
      ons_pos_get_injective_of_vertices_dropLast_nodup l hnodup
    exact hinj hpos
  subst ib
  rfl


theorem hexCS_cyclicTurnSum_eq_zero_of_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : 0 < dx)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      0 ≤ z.1 ∧ z.1 < dx) :
    ons_cyclicTurnSum l = 0 := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hinj : Function.Injective (ons_periodStateCoord d) :=
    hexCS_periodicCoord_injective_of_slab l dx dy hdisp hdx hnodup hx
  have hnonzero :
      (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨
        (ons_pathDisplacement (List.ofFn d)).2 ≠ 0 := by
    left
    rw [List.ofFn_get, hdisp]
    omega
  have hturn := ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    d hinj hnonzero
  simpa [d] using hturn


theorem hexCS_periodicCoord_injective_of_negative_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : dx < 0)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      dx < z.1 ∧ z.1 ≤ 0) :
    Function.Injective
      (ons_periodStateCoord (fun i : Fin l.length => l.get i)) := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hverts : (ons_pathVertices l).dropLast =
      List.ofFn (StatMech.Onsager.BaseCase.pos d) :=
    ons_pathVertices_dropLast_eq_ofFn_pos l
  intro a b hab
  rcases a with ⟨ra, ia⟩
  rcases b with ⟨rb, ib⟩
  have hpaMem : StatMech.Onsager.BaseCase.pos d ia ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ia, rfl⟩
  have hpbMem : StatMech.Onsager.BaseCase.pos d ib ∈
      (ons_pathVertices l).dropLast := by
    rw [hverts, List.mem_ofFn]
    exact ⟨ib, rfl⟩
  have hxa := hx _ hpaMem
  have hxb := hx _ hpbMem
  have hperiodDisp : ons_pathDisplacement (List.ofFn d) = (dx, dy) := by
    rw [List.ofFn_get]
    exact hdisp
  change StatMech.Onsager.BaseCase.pos d ia +
      ra • ons_pathDisplacement (List.ofFn d) =
    StatMech.Onsager.BaseCase.pos d ib +
      rb • ons_pathDisplacement (List.ofFn d) at hab
  have hfirst := congrArg Prod.fst hab
  rw [hperiodDisp] at hfirst
  simp only [Prod.fst_add, Prod.smul_mk, nsmul_eq_mul] at hfirst
  have hra : ra = rb := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : (ra : ℤ) * dx - (rb : ℤ) * dx ≥ -dx := by
        have hr : (ra : ℤ) + 1 ≤ rb := by exact_mod_cast hlt
        nlinarith
      nlinarith [hfirst]
    · have hstep : (rb : ℤ) * dx - (ra : ℤ) * dx ≥ -dx := by
        have hr : (rb : ℤ) + 1 ≤ ra := by exact_mod_cast hgt
        nlinarith
      nlinarith [hfirst]
  subst rb
  have hpos : StatMech.Onsager.BaseCase.pos d ia =
      StatMech.Onsager.BaseCase.pos d ib := by
    simpa [ons_periodStateCoord] using hab
  have hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup l hnodup
  have hib : ia = ib := hinj hpos
  subst ib
  rfl


theorem hexCS_cyclicTurnSum_eq_zero_of_negative_slab
    (l : List (Fin 4)) [NeZero l.length] (dx dy : ℤ)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hdx : dx < 0)
    (hnodup : (ons_pathVertices l).dropLast.Nodup)
    (hx : ∀ z ∈ (ons_pathVertices l).dropLast,
      dx < z.1 ∧ z.1 ≤ 0) :
    ons_cyclicTurnSum l = 0 := by
  let d : Fin l.length → Fin 4 := fun i => l.get i
  have hinj : Function.Injective (ons_periodStateCoord d) :=
    hexCS_periodicCoord_injective_of_negative_slab
      l dx dy hdisp hdx hnodup hx
  have hnonzero :
      (ons_pathDisplacement (List.ofFn d)).1 ≠ 0 ∨
        (ons_pathDisplacement (List.ofFn d)).2 ≠ 0 := by
    left
    rw [List.ofFn_get, hdisp]
    omega
  have hturn := ons_periodicSimple_cyclicTurnSum_eq_zero_of_nonzero
    d hinj hnonzero
  simpa [d] using hturn


theorem hexCSCoordPath_eq_prefixCoords
    (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) ts =
      hexCSOutsideStartCoord ::
        List.ofFn (fun k : Fin (ts.length + 1) =>
          hexEndpointPrefixCoord ts hlegal k.val) := by
  apply hexAWPos_injective.list_map
  rw [hexCSCoordPath_start_pos ts hlegal]
  congr 1
  apply List.ext_getElem
  · simp [length_verticesAux]
  · intro k hk hk'
    have hkle : k ≤ ts.length := by
      rw [length_verticesAux] at hk
      omega
    have hget := hexJordan_verticesAux_getElem?_eq
      hexAWStart 1 ts k hkle
    rw [List.getElem?_eq_getElem hk, Option.some.injEq] at hget
    rw [List.getElem_map, List.getElem_ofFn]
    have hp := hexEndpointPrefixCoord_pos ts hlegal k
    unfold hexJordan_vertexPos at hp
    exact hget.trans hp


theorem hexCS_finalPrefixCoord_eq_outside
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexEndpointPrefixCoord ts hadm.1.1 ts.length =
      hexAWNeighbor e.vtx.1 e.edge := by
  apply hexAWPos_injective
  rw [← hexEndpointPrefixCoord_pos ts hadm.1.1 ts.length]
  have hx := hexCS_endpoint_boundary_exit e ts he hne hadm
  calc
    hexJordan_vertexPos hexAWStart 1 ts ts.length =
        hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) := by
      simp [hexJordan_vertexPos]
    _ = hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e) := hx
    _ = hexAWPos (hexAWNeighbor e.vtx.1 e.edge) := by
      rw [hexCSCanonicalHeading_halfStep]
      exact (hexAWNeighborPos_eq_mid_add e.vtx.1 e.edge).symm


theorem hexCSOutsideStart_ne_endpointOutside
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT) :
    hexCSOutsideStartCoord ≠ hexAWNeighbor e.vtx.1 e.edge := by
  intro hout
  have hmidMem : hexAWMid e.vtx.1 e.edge ∈ hexCSMids T L := by
    rw [hexCSMids, Finset.mem_biUnion]
    refine ⟨e.vtx, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    exact ⟨e.edge, Finset.mem_univ _, rfl⟩
  have houtsideMid :
      hexAWMid hexCSOutsideStartCoord e.edge ∈ hexCSMids T L := by
    rw [hout, hexAWMid_neighbor]
    exact hmidMem
  have hedge : e.edge = 0 :=
    (hexCSOutsideStart_mid_mem_iff T L hT e.edge).mp houtsideMid
  apply hne
  apply hexCSBoundaryIncidence_eq_start_of_mid e
  calc
    hexAWMid e.vtx.1 e.edge =
        hexAWMid (hexAWNeighbor e.vtx.1 e.edge) e.edge :=
      (hexAWMid_neighbor e.vtx.1 e.edge).symm
    _ = hexAWMid hexCSOutsideStartCoord 0 := by rw [← hout, hedge]
    _ = hexAWStart := hexCSOutsideStart_mid_zero


theorem hexCSCoordPath_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    (hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) ts).Nodup := by
  rw [hexCSCoordPath_eq_prefixCoords ts hadm.1.1,
    List.nodup_cons]
  constructor
  · rw [List.mem_ofFn]
    rintro ⟨k, hk⟩
    by_cases hlast : k.val = ts.length
    · have hfinal := hexCS_finalPrefixCoord_eq_outside e ts he hne hadm
      rw [hlast, hfinal] at hk
      exact hexCSOutsideStart_ne_endpointOutside e he hne hk.symm
    · have hklt : k.val < ts.length := by omega
      have hmem := hexCS_prefixCoord_mem ts ⟨hadm.1, hadm.2.1⟩
        k.val hklt
      rw [hk] at hmem
      have hout : hexCSOutsideStartCoord ∉ hexCSVertexSet T L := by
        rw [hexCS_mem_vertexSet_iff]
        simp [hexCSOutsideStartCoord, hexCSInStrip,
          hexAWBookRe2, hexAWDepth, hexAWLong]
      exact hout hmem
  · rw [List.nodup_ofFn]
    intro i j hij
    change hexEndpointPrefixCoord ts hadm.1.1 i.val =
      hexEndpointPrefixCoord ts hadm.1.1 j.val at hij
    by_cases hilast : i.val = ts.length
    · by_cases hjlast : j.val = ts.length
      · apply Fin.ext
        omega
      · have hjlt : j.val < ts.length := by omega
        have hfinal := hexCS_finalPrefixCoord_eq_outside e ts he hne hadm
        have hjmem := hexCS_prefixCoord_mem ts ⟨hadm.1, hadm.2.1⟩
          j.val hjlt
        rw [hilast, hfinal] at hij
        rw [← hij] at hjmem
        exact (hexCSOutsideBoundary_not_mem e he hjmem).elim
    · by_cases hjlast : j.val = ts.length
      · have hilt : i.val < ts.length := by omega
        have hfinal := hexCS_finalPrefixCoord_eq_outside e ts he hne hadm
        have himem := hexCS_prefixCoord_mem ts ⟨hadm.1, hadm.2.1⟩
          i.val hilt
        rw [hjlast, hfinal] at hij
        rw [hij] at himem
        exact (hexCSOutsideBoundary_not_mem e he himem).elim
      · have hilt : i.val < ts.length := by omega
        have hjlt : j.val < ts.length := by omega
        apply Fin.ext
        by_contra hval
        apply (hexEndpoint_vertexPos_ne_of_saw ts hadm.1.2
          i.val j.val hilt hjlt hval)
        rw [hexEndpointPrefixCoord_pos ts hadm.1.1 i.val,
          hexEndpointPrefixCoord_pos ts hadm.1.1 j.val]
        exact congrArg hexAWPos hij


end
end StatMech.Universality
