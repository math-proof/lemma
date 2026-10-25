/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicAtomSupport
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointPieceRigidity
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointTripletOrbit
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripLocal


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCS_edge_flank_parity
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (hsimple : Function.Injective (StatMech.Onsager.BaseCase.pos d))
    (hlen : 3 ≤ n) (k : Fin n) :
    JordanParity.rayParity d
        (Orientation.leftCell (d k) (StatMech.Onsager.BaseCase.pos d k)).1
        (Orientation.leftCell (d k) (StatMech.Onsager.BaseCase.pos d k)).2 =
      JordanParity.rayParity d
          (hexCSRightCell (d k) (StatMech.Onsager.BaseCase.pos d k)).1
          (hexCSRightCell (d k) (StatMech.Onsager.BaseCase.pos d k)).2 + 1 := by
  have hs := StatMech.Onsager.NoDoubleWind.pos_succ d hclosed k
  generalize hp : StatMech.Onsager.BaseCase.pos d k = p at hs ⊢
  obtain ⟨x, y⟩ := p
  generalize hd : d k = w at hs ⊢
  fin_cases w
  · have hmid : k ∈ RayFlipV.midSet d x y := by
      simp only [RayFlipV.midSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨Or.inl hd, ?_, ?_⟩
      · rw [hp]
        simp [hs, hd, StatMech.Onsager.BaseCase.stepOf]
      · rw [hp]
    have hf := RayFlipV.rayParity_vflip d x (y - 1) (by
      rw [show y - 1 + 1 = y by ring]
      exact EdgeUnique.midSet_card_odd_of_mem d hclosed hsimple hlen
        x y k hmid)
    simp only [Orientation.leftCell, hexCSRightCell, hp, hd]
    rw [show y - 1 + 1 = y by ring] at hf
    calc
      JordanParity.rayParity d x y =
          (JordanParity.rayParity d x y + 1) + 1 :=
        GeneralUmlaufsatz.zmod2_add_one_add_one _
      _ = JordanParity.rayParity d x (y - 1) + 1 := by rw [hf]
  · have hstr : k ∈ RayFlipH.straddleSet d (x - 1) y := by
      simp only [RayFlipH.straddleSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨Or.inl hd, ?_, ?_, ?_⟩
      · rw [hp]
        simp
      · rw [hp, hs]
        simp [StatMech.Onsager.BaseCase.stepOf]
      · rw [hp, hs]
        simp [StatMech.Onsager.BaseCase.stepOf]
    have hf := RayFlipH.rayParity_hflip d hclosed (x - 1) y
      (EdgeUnique.straddleSet_card_odd_of_mem d hclosed hsimple hlen
        (x - 1) y k hstr)
    simpa only [Orientation.leftCell, hexCSRightCell, hp, hd,
      show x - 1 + 1 = x by ring] using hf
  · have hmid : k ∈ RayFlipV.midSet d (x - 1) y := by
      simp only [RayFlipV.midSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨Or.inr hd, ?_, ?_⟩
      · rw [hp, hs]
        simp [StatMech.Onsager.BaseCase.stepOf]
        ring
      · rw [hp]
    have hf := RayFlipV.rayParity_vflip d (x - 1) (y - 1) (by
      rw [show y - 1 + 1 = y by ring]
      exact EdgeUnique.midSet_card_odd_of_mem d hclosed hsimple hlen
        (x - 1) y k hmid)
    simpa only [Orientation.leftCell, hexCSRightCell, hp, hd,
      show y - 1 + 1 = y by ring] using hf
  · have hstr : k ∈ RayFlipH.straddleSet d (x - 1) (y - 1) := by
      simp only [RayFlipH.straddleSet, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨Or.inr hd, ?_, ?_, ?_⟩
      · rw [hp]
        simp
      · rw [hp, hs]
        simp [StatMech.Onsager.BaseCase.stepOf]
      · rw [hp, hs]
        simp [StatMech.Onsager.BaseCase.stepOf]
    have hf := RayFlipH.rayParity_hflip d hclosed (x - 1) (y - 1)
      (EdgeUnique.straddleSet_card_odd_of_mem d hclosed hsimple hlen
        (x - 1) (y - 1) k hstr)
    simp only [Orientation.leftCell, hexCSRightCell, hp, hd]
    rw [show x - 1 + 1 = x by ring] at hf
    calc
      JordanParity.rayParity d x (y - 1) =
          (JordanParity.rayParity d x (y - 1) + 1) + 1 :=
        GeneralUmlaufsatz.zmod2_add_one_add_one _
      _ = JordanParity.rayParity d (x - 1) (y - 1) + 1 := by rw [hf]


theorem hexCS_rayParity_zero_of_diag_below
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (s : ℤ × ℤ)
    (hdepth : ∀ k : Fin n,
      s.2 - s.1 < (StatMech.Onsager.BaseCase.pos d k).2 -
        (StatMech.Onsager.BaseCase.pos d k).1) :
    JordanParity.rayParity d s.1 s.2 = 0 := by
  have heq : JordanParity.upCross d s.1 s.2 =
      WalkCrossingV.vertColCross d s.1 := by
    unfold JordanParity.upCross WalkCrossingV.vertColCross
    congr 1
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro ⟨hh, hm, _⟩
      exact ⟨hh, hm⟩
    · rintro ⟨hh, hm⟩
      refine ⟨hh, hm, ?_⟩
      have hy := WalkCrossing.horiz_y_const d hclosed k hh
      rcases WalkCrossing.horiz_x_step d hclosed k hh with hx | hx
      · have hk := hdepth k
        rw [hx] at hm
        omega
      · have hk := hdepth (k + 1)
        rw [hx] at hm
        omega
  rw [JordanParity.rayParity, heq]
  obtain ⟨r, hr⟩ := WalkCrossingV.vertColCross_even d hclosed s.1
  rw [hr]
  push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]


theorem hexCS_rayParity_eq_of_adjacent_nonvertices
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (p : ℤ × ℤ) (w : Fin 4)
    (hp : ∀ k : Fin n, StatMech.Onsager.BaseCase.pos d k ≠ p)
    (hq : ∀ k : Fin n, StatMech.Onsager.BaseCase.pos d k ≠
      p + StatMech.Onsager.BaseCase.stepOf w) :
    JordanParity.rayParity d p.1 p.2 =
      JordanParity.rayParity d
        (p + StatMech.Onsager.BaseCase.stepOf w).1
        (p + StatMech.Onsager.BaseCase.stepOf w).2 := by
  have hp' := WalkCellBridge.rayParity_const_of_not_vertex
    d hclosed p.1 p.2 hp
  let q := p + StatMech.Onsager.BaseCase.stepOf w
  have hq' := WalkCellBridge.rayParity_const_of_not_vertex
    d hclosed q.1 q.2 hq
  fin_cases w
  · simpa [q, StatMech.Onsager.BaseCase.stepOf] using hq'.1
  · simpa [q, StatMech.Onsager.BaseCase.stepOf] using hq'.2.1
  · simpa [q, StatMech.Onsager.BaseCase.stepOf] using hp'.1.symm
  · simpa [q, StatMech.Onsager.BaseCase.stepOf] using hp'.2.1.symm


theorem hexCS_rayParity_eq_along_avoiding_path
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (s : ℤ × ℤ) (l : List (Fin 4))
    (havoid : ∀ p ∈ ons_pathVertices l, ∀ k : Fin n,
      StatMech.Onsager.BaseCase.pos d k ≠ s + p) :
    JordanParity.rayParity d s.1 s.2 =
      JordanParity.rayParity d
        (s + ons_pathDisplacement l).1
        (s + ons_pathDisplacement l).2 := by
  induction l generalizing s with
  | nil => simp
  | cons w ws ih =>
      let q := s + StatMech.Onsager.BaseCase.stepOf w
      have hs : ∀ k : Fin n,
          StatMech.Onsager.BaseCase.pos d k ≠ s := by
        intro k
        simpa using havoid 0 (by simp) k
      have hq : ∀ k : Fin n,
          StatMech.Onsager.BaseCase.pos d k ≠ q := by
        intro k
        have hm : StatMech.Onsager.BaseCase.stepOf w ∈
            ons_pathVertices (w :: ws) := by
          rw [ons_pathVertices_cons]
          right
          have hzero : (0 : ℤ × ℤ) ∈ ons_pathVertices ws := by
            cases ws <;> simp [ons_pathVertices]
          exact List.mem_map.mpr
            ⟨(0 : ℤ × ℤ), hzero, add_zero _⟩
        simpa only [q, add_zero] using
          havoid (StatMech.Onsager.BaseCase.stepOf w) hm k
      have hstep := hexCS_rayParity_eq_of_adjacent_nonvertices
        d hclosed s w hs (by simpa only [q] using hq)
      have htail : ∀ p ∈ ons_pathVertices ws, ∀ k : Fin n,
          StatMech.Onsager.BaseCase.pos d k ≠ q + p := by
        intro p hp k
        have hm : StatMech.Onsager.BaseCase.stepOf w + p ∈
            ons_pathVertices (w :: ws) := by
          rw [ons_pathVertices_cons]
          right
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        simpa only [q, add_assoc] using
          havoid (StatMech.Onsager.BaseCase.stepOf w + p) hm k
      calc
        JordanParity.rayParity d s.1 s.2 =
            JordanParity.rayParity d q.1 q.2 := by
          simpa only [q] using hstep
        _ = JordanParity.rayParity d
            (q + ons_pathDisplacement ws).1
            (q + ons_pathDisplacement ws).2 := ih q htail
        _ = JordanParity.rayParity d
            (s + ons_pathDisplacement (w :: ws)).1
            (s + ons_pathDisplacement (w :: ws)).2 := by
          congr 2 <;> simp only [q, ons_pathDisplacement_cons] <;> abel

theorem hexCS_pathVertices_dropLast_directions
    (l : List (Fin 4)) (hne : l ≠ []) :
    ons_pathVertices l.dropLast = (ons_pathVertices l).dropLast := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons w ws ih =>
      cases ws with
      | nil => rfl
      | cons v vs =>
          have htail : v :: vs ≠ [] := List.cons_ne_nil _ _
          rw [List.dropLast_cons_of_ne_nil htail]
          change
            0 :: (ons_pathVertices (v :: vs).dropLast).map
                (StatMech.Onsager.BaseCase.stepOf w + ·) =
              (0 :: (ons_pathVertices (v :: vs)).map
                (StatMech.Onsager.BaseCase.stepOf w + ·)).dropLast
          have hmap : (ons_pathVertices (v :: vs)).map
              (StatMech.Onsager.BaseCase.stepOf w + ·) ≠ [] := by simp
          rw [List.dropLast_cons_of_ne_nil hmap, ← List.map_dropLast,
            ih htail]


theorem HexEndpointLocalCrossing.source_terminal_geometry
    {T L : ℕ} {hT : 0 < T} {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let tail := ts.drop (C.index + 1)
    let h := hexInfra_headAccum 1 base
    let prefixCoords :=
      (hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) base).dropLast
    let terminalCoords :=
      (hexCSCoordPath c (hexCSHeadingFin (h + t)) tail).dropLast
    prefixCoords.Disjoint terminalCoords ∧
      ∀ q ∈ terminalCoords, q ∈ hexCSVertexSet T L := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  let prefixCoords :=
    (hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) base).dropLast
  let terminalCoords :=
    (hexCSCoordPath c (hexCSHeadingFin (h + t)) tail).dropLast
  dsimp only
  have hbase : ∀ u ∈ base, u = 1 ∨ u = -1 := by
    intro u hu
    exact hadm.1.1 u (List.mem_of_mem_take hu)
  have hsplit : ts = base ++ t :: tail := by
    calc
      ts = ts.take C.index ++ ts.drop C.index :=
        (List.take_append_drop C.index ts).symm
      _ = base ++ t :: tail := by
        rw [List.drop_eq_getElem_cons C.index_lt]
  have hpmap : prefixCoords.map hexAWPos =
      hexAWPos hexCSOutsideStartCoord ::
        (verticesAux hexAWStart 1 base).dropLast := by
    have hp := congrArg List.dropLast
      (hexCSCoordPath_start_pos base hbase)
    rw [← List.map_dropLast] at hp
    rw [List.dropLast_cons_of_ne_nil
      (hexInfra_verticesAux_ne_nil hexAWStart 1 base)] at hp
    simpa only [prefixCoords] using hp
  have htmap : terminalCoords.map hexAWPos =
      (verticesAux m h (t :: tail)).dropLast := by
    have hp := congrArg List.dropLast (C.terminalCoordPath_pos hadm.1)
    rw [← List.map_dropLast] at hp
    simpa only [base, t, tail, m, h, terminalCoords] using hp
  have hconcat : (prefixCoords ++ terminalCoords).map hexAWPos =
      hexAWPos hexCSOutsideStartCoord ::
        (verticesAux hexAWStart 1 ts).dropLast := by
    rw [List.map_append, hpmap, htmap, hsplit,
      hexEndpoint_dropLast_verticesAux_append]
    simp only [m, h, List.cons_append]
  have hout : hexAWPos hexCSOutsideStartCoord ∉
      (verticesAux hexAWStart 1 ts).dropLast := by
    intro hout
    have hout' : hexAWPos hexCSOutsideStartCoord ∈
        (ofTurns hexAWStart 1 ts).endpointVertices := hout
    obtain ⟨q, hq, hpos⟩ := hexCS_endpointVertex_inside ts
      hadm _ hout'
    have hqc : q = hexCSOutsideStartCoord :=
      hexAWPos_injective hpos.symm
    rw [hqc, hexCS_mem_vertexSet_iff] at hq
    simp [hexCSOutsideStartCoord, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hq
  have hcoord : (prefixCoords ++ terminalCoords).Nodup := by
    apply (List.nodup_map_iff hexAWPos_injective).mp
    rw [hconcat, List.nodup_cons]
    exact ⟨hout, hadm.1.2⟩
  constructor
  · rw [List.disjoint_iff_ne]
    intro q hq r hr
    apply (List.nodup_append.mp hcoord).2.2 q
      (by simpa only [prefixCoords] using hq) r
      (by simpa only [terminalCoords] using hr)
  · intro q hq
    have hqposSuffix : hexAWPos q ∈
        (verticesAux m h (t :: tail)).dropLast := by
      rw [← htmap, List.mem_map]
      exact ⟨q, hq, rfl⟩
    have hqpos : hexAWPos q ∈
        (ofTurns hexAWStart 1 ts).endpointVertices := by
      change hexAWPos q ∈ (verticesAux hexAWStart 1 ts).dropLast
      rw [hsplit, hexEndpoint_dropLast_verticesAux_append,
        List.mem_append]
      exact Or.inr hqposSuffix
    obtain ⟨r, hr, hqr⟩ := hexCS_endpointVertex_inside ts
      hadm _ hqpos
    exact (hexAWPos_injective hqr).symm ▸ hr


theorem HexEndpointLocalCrossing.terminal_stem_exterior
    {T L : ℕ} {hT : 0 < T} {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (endEdge : Fin 3)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let tail := ts.drop (C.index + 1)
    let h := hexInfra_headAccum 1 base
    let dirs := hexCSBrickDirections (h + t) tail
    let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
    let stemDirs := (hexCSBrickDirections 1 base).dropLast
    let s := hexBrickPos hexCSOutsideStartCoord - hexBrickPos c
    JordanParity.rayParity d (s + ons_pathDisplacement stemDirs).1
        (s + ons_pathDisplacement stemDirs).2 = 0 ∧
      ∀ k : Fin dirs.length, StatMech.Onsager.BaseCase.pos d k ≠
        s + ons_pathDisplacement stemDirs := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let h := hexInfra_headAccum 1 base
  let dirs := hexCSBrickDirections (h + t) tail
  let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
  let stemDirs := (hexCSBrickDirections 1 base).dropLast
  let s := hexBrickPos hexCSOutsideStartCoord - hexBrickPos c
  let prefixCoords :=
    (hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) base).dropLast
  let terminalCoords :=
    (hexCSCoordPath c (hexCSHeadingFin (h + t)) tail).dropLast
  dsimp only
  have htail : ∀ u ∈ tail, u = 1 ∨ u = -1 := by
    intro u hu
    exact hadm.1.1 u (List.mem_of_mem_drop hu)
  have hbase : ∀ u ∈ base, u = 1 ∨ u = -1 := by
    intro u hu
    exact hadm.1.1 u (List.mem_of_mem_take hu)
  have hgeom := C.terminalBrick_closed_nodup hnotOutside hadm.1
    endEdge hadm.2.2 hcount
  have hclosed : ons_pathDisplacement dirs = 0 := by
    simpa only [base, t, tail, h, dirs] using hgeom.1
  have hsum : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hedge := C.edgeOf_after_heading hadm.1
  have htbrick : terminalCoords.map
      (fun q => hexBrickPos q - hexBrickPos c) =
        (ons_pathVertices dirs).dropLast := by
    have hb := hexCSCoordPath_brick c (h + t) tail hedge.1 htail
    have hb' := congrArg List.dropLast hb
    rw [← List.map_dropLast] at hb'
    simpa only [terminalCoords, dirs] using hb'
  have hpbrick : prefixCoords.map
      (fun q => hexBrickPos q - hexBrickPos hexCSOutsideStartCoord) =
        ons_pathVertices stemDirs := by
    have hb := hexCSCoordPath_brick hexCSOutsideStartCoord 1 base
      hexCSHeadingFits_start hbase
    have hb' := congrArg List.dropLast hb
    rw [← List.map_dropLast] at hb'
    have hdne : hexCSBrickDirections 1 base ≠ [] :=
      hexCSBrickDirections_ne_nil 1 base
    change prefixCoords.map
      (fun q => hexBrickPos q - hexBrickPos hexCSOutsideStartCoord) =
        ons_pathVertices (hexCSBrickDirections 1 base).dropLast
    rw [hexCS_pathVertices_dropLast_directions
      (hexCSBrickDirections 1 base) hdne]
    simpa only [prefixCoords] using hb'
  have hst := C.source_terminal_geometry
    ⟨hadm.1, hadm.2.1⟩
  have hdis : prefixCoords.Disjoint terminalCoords := by
    simpa only [base, t, tail, h, prefixCoords, terminalCoords] using hst.1
  have hin : ∀ q ∈ terminalCoords, q ∈ hexCSVertexSet T L := by
    simpa only [base, t, tail, h, terminalCoords] using hst.2
  have hdepth : ∀ k : Fin dirs.length,
      s.2 - s.1 < (StatMech.Onsager.BaseCase.pos d k).2 -
        (StatMech.Onsager.BaseCase.pos d k).1 := by
    intro k
    have hk : StatMech.Onsager.BaseCase.pos d k ∈
        (ons_pathVertices dirs).dropLast := by
      rw [ons_pathVertices_dropLast_eq_ofFn_pos]
      rw [List.mem_ofFn]
      exact ⟨k, by simp [d]⟩
    rw [← htbrick, List.mem_map] at hk
    obtain ⟨q, hq, hqpos⟩ := hk
    have hqin := hin q hq
    have hd := hexCS_inside_brick_depth_pos q hqin
    rw [Prod.ext_iff] at hqpos
    simp only [s, Prod.fst_sub, Prod.snd_sub] at hd hqpos ⊢
    omega
  have hsource : JordanParity.rayParity d s.1 s.2 = 0 :=
    hexCS_rayParity_zero_of_diag_below d hsum s hdepth
  have havoid : ∀ p ∈ ons_pathVertices stemDirs,
      ∀ k : Fin dirs.length,
        StatMech.Onsager.BaseCase.pos d k ≠ s + p := by
    intro p hp k heq
    rw [← hpbrick, List.mem_map] at hp
    obtain ⟨q, hq, hqpos⟩ := hp
    have hk : StatMech.Onsager.BaseCase.pos d k ∈
        (ons_pathVertices dirs).dropLast := by
      rw [ons_pathVertices_dropLast_eq_ofFn_pos, List.mem_ofFn]
      exact ⟨k, by simp [d]⟩
    rw [← htbrick, List.mem_map] at hk
    obtain ⟨r, hr, hrpos⟩ := hk
    apply (List.disjoint_iff_ne.mp hdis) q hq r hr
    apply hexBrickPos_injective
    rw [Prod.ext_iff] at hqpos hrpos heq ⊢
    simp only [s, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub] at hqpos hrpos heq ⊢
    constructor <;> omega
  have htransport := hexCS_rayParity_eq_along_avoiding_path
    d hsum s stemDirs havoid
  constructor
  · exact htransport.symm.trans hsource
  · intro k
    apply havoid (ons_pathDisplacement stemDirs)
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp
      (ons_pathVertices_getLast stemDirs)
    rw [hys]
    simp


theorem HexEndpointLocalCrossing.terminal_stem_point_eq_before
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    let base := ts.take C.index
    let h := hexInfra_headAccum 1 base
    let stemDirs := (hexCSBrickDirections 1 base).dropLast
    let s := hexBrickPos hexCSOutsideStartCoord - hexBrickPos c
    s + ons_pathDisplacement stemDirs =
      hexBrickPos (hexAWNeighbor c C.before) - hexBrickPos c := by
  let base := ts.take C.index
  let m := hexInfra_midAccum hexAWStart 1 base
  let h := hexInfra_headAccum 1 base
  let fullDirs := hexCSBrickDirections 1 base
  let stemDirs := fullDirs.dropLast
  let s := hexBrickPos hexCSOutsideStartCoord - hexBrickPos c
  let coords := hexCSCoordPath hexCSOutsideStartCoord (hexCSHeadingFin 1) base
  dsimp only
  have hbase : ∀ u ∈ base, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_take hu)
  have hlast : coords.getLast? = some c := by
    change (hexCSCoordPath hexCSOutsideStartCoord
      (hexCSHeadingFin 1) base).getLast? = some c
    rw [hexCSCoordPath_eq_prefixCoords base hbase,
      List.getLast?_eq_getLast (by simp), List.getLast_cons (by simp),
      List.getLast_ofFn (by simp)]
    apply congrArg some
    apply hexAWPos_injective
    change hexAWPos (hexEndpointPrefixCoord base hbase base.length) =
      hexAWPos c
    have hp := hexEndpointPrefixCoord_pos base hbase base.length
    unfold hexJordan_vertexPos at hp
    rw [List.take_length] at hp
    rw [← C.at_vertex]
    simpa only [base, m, h] using hp.symm
  have hb := hexCSCoordPath_brick hexCSOutsideStartCoord 1 base
    hexCSHeadingFits_start hbase
  have hlastBrick := congrArg List.getLast? hb
  rw [List.getLast?_map, hlast, ons_pathVertices_getLast] at hlastBrick
  have hdisp : ons_pathDisplacement fullDirs =
      hexBrickPos c - hexBrickPos hexCSOutsideStartCoord := by
    simpa only [fullDirs, coords, Option.map_some, Option.some.injEq]
      using hlastBrick.symm
  have hdne : fullDirs ≠ [] := hexCSBrickDirections_ne_nil 1 base
  have hlastDir : fullDirs.getLast hdne =
      hexBrickDir (hexCSHeadingFin h) := by
    have hg := hexCSBrickDirections_getLast 1 base
    rw [ons_getLast!_eq_getLast fullDirs hdne] at hg
    simpa only [fullDirs, h] using hg
  have hrecon : stemDirs ++ [hexBrickDir (hexCSHeadingFin h)] =
      fullDirs := by
    simpa only [stemDirs, hlastDir] using
      (List.dropLast_append_getLast hdne)
  have hsplit := congrArg ons_pathDisplacement hrecon
  rw [ons_pathDisplacement_append] at hsplit
  simp only [ons_pathDisplacement_cons, ons_pathDisplacement_nil, add_zero]
    at hsplit
  have hhalf : halfStep h = halfStep (hexAWHeading c C.before + 3) := by
    calc
      halfStep h = hexAWPos c - m := by
        linear_combination C.at_vertex
      _ = -(hexAWMid c C.before - hexAWPos c) := by
        rw [← C.before_mid]
        ring
      _ = -halfStep (hexAWHeading c C.before) := by
        rw [hexAWMid_sub_pos_eq_halfStep]
      _ = halfStep (hexAWHeading c C.before + 3) :=
        (hexEndpoint_halfStep_add_three _).symm
  have hh : hexCSHeadingFin h =
      hexCSHeadingFin (hexAWHeading c C.before + 3) :=
    hexCSHeadingFin_eq_of_halfStep_eq _ _ hhalf
  have hopp : -StatMech.Onsager.BaseCase.stepOf
        (hexBrickDir (hexCSHeadingFin h)) =
      StatMech.Onsager.BaseCase.stepOf
        (hexBrickDir (hexAWHeadingMod c C.before)) := by
    rw [hh, hexCSHeadingFin_hexAWHeading_add_three]
    rcases c with ⟨i, j, color⟩
    generalize hb : C.before = b
    cases color <;> fin_cases b <;> rfl
  have hn := hexBrickPos_neighbor c C.before
  change s + ons_pathDisplacement stemDirs =
    hexBrickPos (hexAWNeighbor c C.before) - hexBrickPos c
  rw [Prod.ext_iff] at hdisp hsplit hopp hn ⊢
  simp only [s, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub, Prod.fst_neg, Prod.snd_neg] at hdisp hsplit hopp hn ⊢
  constructor <;> omega

set_option maxHeartbeats 1000000 in


theorem hexCS_terminal_side_of_exterior_stem
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (hsimple : Function.Injective (StatMech.Onsager.BaseCase.pos d))
    (hlen : 3 ≤ n) (c : HexAWCoord) (before after endEdge : Fin 3)
    (hfirst : d 0 = hexBrickDir (hexAWHeadingMod c after))
    (hlast : d (ons_lastFin n) =
      hexBrickDir (hexAWHeadingMod c endEdge + 3))
    (hexterior : JordanParity.rayParity d
      (hexBrickPos (hexAWNeighbor c before) - hexBrickPos c).1
      (hexBrickPos (hexAWNeighbor c before) - hexBrickPos c).2 = 0)
    (hstem : ∀ k : Fin n, StatMech.Onsager.BaseCase.pos d k ≠
      hexBrickPos (hexAWNeighbor c before) - hexBrickPos c) :
    (after = hexCyclicPred before ∧ endEdge = hexCyclicSucc before →
        Orientation.leftParity d 0 = 1) ∧
      (after = hexCyclicSucc before ∧ endEdge = hexCyclicPred before →
        Orientation.leftParity d 0 ≠ 1) := by
  let q := hexBrickPos (hexAWNeighbor c before) - hexBrickPos c
  let last := ons_lastFin n
  have hq := WalkCellBridge.rayParity_const_of_not_vertex
    d hclosed q.1 q.2 (by simpa only [q] using hstem)
  have hzero : StatMech.Onsager.BaseCase.pos d (0 : Fin n) = 0 :=
    StatMech.Onsager.NoDoubleWind.pos_zero d
  have hwrap : last + 1 = (0 : Fin n) := by
    apply Fin.ext
    simp only [last, ons_lastFin, Fin.val_add, Fin.val_one', Fin.val_zero]
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [Nat.mod_eq_of_lt (by omega : 1 < n), Nat.sub_add_cancel (by omega)]
    exact Nat.mod_self n
  have hplast : StatMech.Onsager.BaseCase.pos d last =
      -StatMech.Onsager.BaseCase.stepOf (d last) := by
    have hs := StatMech.Onsager.NoDoubleWind.pos_succ d hclosed last
    rw [hwrap, hzero] at hs
    rw [Prod.ext_iff] at hs ⊢
    simp only [Prod.fst_zero, Prod.snd_zero, Prod.fst_add, Prod.snd_add,
      Prod.fst_neg, Prod.snd_neg] at hs ⊢
    constructor <;> omega
  have hflank0 := hexCS_edge_flank_parity d hclosed hsimple hlen (0 : Fin n)
  have hflankLast := hexCS_edge_flank_parity d hclosed hsimple hlen last
  rcases hq with ⟨hqWest, hqSouth, hqSouthWest⟩
  constructor
  · rintro ⟨ha, he⟩
    rw [ha] at hfirst
    rw [he] at hlast
    rcases c with ⟨ci, cj, color⟩
    generalize hb : before = b
    cases color <;> fin_cases b <;>
      simp [q, hb, hexCyclicPred, hexCyclicSucc, hexAWNeighbor,
        hexBrickPos, hexAWHeadingMod,
        hexBrickDir, StatMech.Onsager.BaseCase.stepOf]
        at hexterior hqWest hqSouth hqSouthWest hfirst hlast <;>
      ring_nf at hexterior hqWest hqSouth hqSouthWest <;>
      simp [last, hfirst, hlast, hzero, hplast, Orientation.leftParity,
        Orientation.leftCell, hexCSRightCell,
        StatMech.Onsager.BaseCase.stepOf] at hflank0 hflankLast ⊢ <;>
      simp [hexterior, hqWest, hqSouth, hqSouthWest]
        at hflank0 hflankLast ⊢ <;>
      assumption
  · rintro ⟨ha, he⟩
    rw [ha] at hfirst
    rw [he] at hlast
    rcases c with ⟨ci, cj, color⟩
    generalize hb : before = b
    cases color <;> fin_cases b <;>
      simp [q, hb, hexCyclicPred, hexCyclicSucc, hexAWNeighbor,
        hexBrickPos, hexAWHeadingMod,
        hexBrickDir, StatMech.Onsager.BaseCase.stepOf]
        at hexterior hqWest hqSouth hqSouthWest hfirst hlast <;>
      ring_nf at hexterior hqWest hqSouth hqSouthWest <;>
      simp [last, hfirst, hlast, hzero, hplast, Orientation.leftParity,
        Orientation.leftCell, hexCSRightCell,
        StatMech.Onsager.BaseCase.stepOf] at hflank0 hflankLast ⊢ <;>
      simp [hexterior, hqWest, hqSouth, hqSouthWest]
        at hflank0 hflankLast ⊢
    all_goals
      first
      | assumption
      | intro hcontra
        have hz := hflank0.trans hflankLast.symm
        rw [hcontra] at hz
        exact one_ne_zero hz


theorem HexEndpointLocalCrossing.terminal_selected_side
    {T L : ℕ} {hT : 0 < T} {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (endEdge : Fin 3)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    let base := ts.take C.index
    let t := ts[C.index]'C.index_lt
    let tail := ts.drop (C.index + 1)
    let h := hexInfra_headAccum 1 base
    HexCSTerminalSelectedSide t h tail := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let h := hexInfra_headAccum 1 base
  let dirs := hexCSBrickDirections (h + t) tail
  let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
  let stemDirs := (hexCSBrickDirections 1 base).dropLast
  let s := hexBrickPos hexCSOutsideStartCoord - hexBrickPos c
  dsimp only
  have hdrop : ts.drop C.index = t :: tail := by
    simpa only [t, tail] using List.drop_eq_getElem_cons C.index_lt
  have hsplit : ts = base ++ t :: tail := by
    calc
      ts = ts.take C.index ++ ts.drop C.index :=
        (List.take_append_drop C.index ts).symm
      _ = base ++ t :: tail := by rw [hdrop]
  have hlenBlock := C.terminalBlock_length_ge_three
    hnotOutside hadm.1 endEdge hadm.2.2 hcount
  have hlen : 3 ≤ dirs.length := by
    simp only [dirs, hexCSBrickDirections_length]
    rw [hdrop] at hlenBlock
    simpa using hlenBlock
  letI : NeZero dirs.length := ⟨by omega⟩
  have hgeom := C.terminalBrick_closed_nodup
    hnotOutside hadm.1 endEdge hadm.2.2 hcount
  have hclosed : ons_pathDisplacement dirs = 0 := by
    simpa only [base, t, tail, h, dirs] using hgeom.1
  have hsum : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup dirs (by
      simpa only [base, t, tail, h, dirs] using hgeom.2)
  have hafter : hexCSHeadingFin (h + t) =
      hexAWHeadingMod c C.after := by
    simpa only [base, t, h] using C.after_heading hadm.1
  have hdne : dirs ≠ [] := hexCSBrickDirections_ne_nil (h + t) tail
  have hfirst : d 0 = hexBrickDir (hexAWHeadingMod c C.after) := by
    calc
      d 0 = dirs.head! := by
        change dirs.get 0 = dirs.head!
        rw [List.get_eq_getElem]
        simp only [Fin.val_zero]
        rw [← List.head_eq_getElem_zero hdne,
          List.head!_eq_head?_getD, List.head?_eq_some_head hdne]
        rfl
      _ = hexBrickDir (hexCSHeadingFin (h + t)) := by
        simpa only [dirs] using hexCSBrickDirections_head (h + t) tail
      _ = hexBrickDir (hexAWHeadingMod c C.after) := by rw [hafter]
  have hhead : hexInfra_headAccum (h + t) tail =
      hexInfra_headAccum 1 ts := by
    rw [hsplit, hexJordan_headAccum_append]
    rfl
  have hfinal := C.final_heading
    hnotOutside hadm.1 endEdge hadm.2.2 hcount
  have hlastGet : d (ons_lastFin dirs.length) = dirs.getLast! := by
    rw [ons_getLast!_eq_getLast dirs hdne]
    exact List.get_length_sub_one (ons_lastFin dirs.length).isLt
  have hlast : d (ons_lastFin dirs.length) =
      hexBrickDir (hexAWHeadingMod c endEdge + 3) := by
    rw [hlastGet, hexCSBrickDirections_getLast, hhead, hfinal,
      hexCSHeadingFin_hexAWHeading_add_three]
  have hstemData := C.terminal_stem_exterior
    hnotOutside endEdge hadm hcount
  have hstemPoint := C.terminal_stem_point_eq_before hadm.1
  have hexterior : JordanParity.rayParity d
      (hexBrickPos (hexAWNeighbor c C.before) - hexBrickPos c).1
      (hexBrickPos (hexAWNeighbor c C.before) - hexBrickPos c).2 = 0 := by
    rw [← hstemPoint]
    simpa only [base, t, tail, h, dirs, d, stemDirs, s]
      using hstemData.1
  have havoid : ∀ k : Fin dirs.length,
      StatMech.Onsager.BaseCase.pos d k ≠
        hexBrickPos (hexAWNeighbor c C.before) - hexBrickPos c := by
    intro k
    rw [← hstemPoint]
    simpa only [base, t, tail, h, dirs, d, stemDirs, s]
      using hstemData.2 k
  have hside := hexCS_terminal_side_of_exterior_stem
    d hsum hinj hlen c C.before C.after endEdge hfirst hlast
      hexterior havoid
  have hafterLabels := C.after_eq_cyclic hadm.1
  have hendLabels := C.endEdge_eq_cyclic
    hnotOutside hadm.1 endEdge hadm.2.2 hcount
  constructor
  · intro ht
    apply hside.1
    exact ⟨hafterLabels.1 ht, hendLabels.1 ht⟩
  · intro ht
    apply hside.2
    exact ⟨hafterLabels.2 ht, hendLabels.2 ht⟩

theorem hexCS_turnSum_sign_of_leftParity
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hsum : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0)
    (hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d))
    (hlen : 3 ≤ n)
    (hnu : ∀ i, d (i + 1) ≠ d i + 2) :
    (Orientation.leftParity d 0 = 1 →
        (∑ i, ons_turnPow (d i) (d (i + 1))) = 4) ∧
      (Orientation.leftParity d 0 ≠ 1 →
        (∑ i, ons_turnPow (d i) (d (i + 1))) = -4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hwalk := GeneralUmlaufsatz.cornerDiff_eq_sign_mul_turnSum
    d hsum hinj hlen hnu
  have hpinch := PinchFree.pinchCount_eq_zero d hsum hinj hlen
  have hchi := GeneralInterior.eulerChar_interiorCells_eq_one d hsum hinj
  have hgb := CellGaussBonnetGlobal.cornerDiff_eq
    (InteriorCells.interiorCells d hsum)
  rw [hchi, hpinch] at hgb
  norm_num at hgb
  constructor
  · intro hleft
    rw [if_pos hleft, one_mul] at hwalk
    exact hwalk.symm.trans hgb
  · intro hright
    rw [if_neg hright] at hwalk
    omega

theorem hexCS_cyclicTurnSum_sign_of_leftParity
    (dirs : List (Fin 4)) [NeZero dirs.length]
    (hclosed : ons_pathDisplacement dirs = 0)
    (hsimple : (ons_pathVertices dirs).dropLast.Nodup)
    (hlen : 3 ≤ dirs.length) :
    let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
    (Orientation.leftParity d 0 = 1 → ons_cyclicTurnSum dirs = 4) ∧
      (Orientation.leftParity d 0 ≠ 1 → ons_cyclicTurnSum dirs = -4) := by
  let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
  dsimp only
  have hsum : ∑ i, StatMech.Onsager.BaseCase.stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (StatMech.Onsager.BaseCase.pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup dirs hsimple
  have hnu := ons_nonUturn_of_pos_injective d hsum hinj hlen
  have hsign := hexCS_turnSum_sign_of_leftParity d hsum hinj hlen hnu
  have hcyc : ons_cyclicTurnSum dirs =
      ∑ i, ons_turnPow (d i) (d (i + 1)) := by
    simpa [d] using ons_cyclicTurnSum_ofFn' d
  constructor
  · intro hleft
    rw [hcyc]
    exact hsign.1 hleft
  · intro hright
    rw [hcyc]
    exact hsign.2 hright


theorem HexEndpointLocalCrossing.selected_terminal_cycle_of_side
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3)
    (hside :
      let base := ts.take C.index
      let t := ts[C.index]'C.index_lt
      let tail := ts.drop (C.index + 1)
      let h := hexInfra_headAccum 1 base
      HexCSTerminalSelectedSide t h tail) :
    (ts[C.index]'C.index_lt = 1 ∧ (ts.drop C.index).sum = -4) ∨
      (ts[C.index]'C.index_lt = -1 ∧ (ts.drop C.index).sum = 4) := by
  let base := ts.take C.index
  let t := ts[C.index]'C.index_lt
  let tail := ts.drop (C.index + 1)
  let h := hexInfra_headAccum 1 base
  let H := hexInfra_headAccum (h + t) tail
  let dirs := hexCSBrickDirections (h + t) tail
  let d : Fin dirs.length → Fin 4 := fun i => dirs.get i
  have ht : t = 1 ∨ t = -1 :=
    hlegal.1 t (List.getElem_mem C.index_lt)
  have htail : ∀ u ∈ tail, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal.1 u (List.mem_of_mem_drop hu)
  have hdrop : ts.drop C.index = t :: tail := by
    simpa only [t, tail] using List.drop_eq_getElem_cons C.index_lt
  have hlen := C.terminalBlock_length_ge_three
    hnotOutside hlegal endEdge hend hcount
  have hlenDirs : 3 ≤ dirs.length := by
    simp only [dirs, hexCSBrickDirections_length]
    rw [hdrop] at hlen
    simpa using hlen
  have hgeom := C.terminalBrick_closed_nodup
    hnotOutside hlegal endEdge hend hcount
  have hclosed : ons_pathDisplacement dirs = 0 := by
    simpa only [base, t, tail, h, dirs] using hgeom.1
  have hsimple : (ons_pathVertices dirs).dropLast.Nodup := by
    simpa only [base, t, tail, h, dirs] using hgeom.2
  have hsign := hexCS_cyclicTurnSum_sign_of_leftParity
    dirs hclosed hsimple hlenDirs
  have hopen := hexCS_brick_open_telescope (h + t) tail htail
  have hclosing := C.closing_brick_identity
    hnotOutside hlegal endEdge hend hcount
  have hclosing' : 2 * (-t) + 3 * ons_turnPow
      (hexBrickDir (hexCSHeadingFin H))
      (hexBrickDir (hexCSHeadingFin (h + t))) =
    hexBrickTurnPotential (hexCSHeadingFin (h + t)) -
      hexBrickTurnPotential (hexCSHeadingFin H) := by
    simpa only [base, t, tail, h, H] using hclosing
  have hcyc : ons_cyclicTurnSum dirs = ons_openTurnSum dirs +
      ons_turnPow (hexBrickDir (hexCSHeadingFin H))
        (hexBrickDir (hexCSHeadingFin (h + t))) := by
    have hdne : dirs ≠ [] := by
      intro hd
      have := congrArg List.length hd
      simp [dirs] at this
    have hc := hexCS_cyclicTurnSum_eq_open_add_close dirs hdne
    simpa only [dirs, hexCSBrickDirections_getLast,
      hexCSBrickDirections_head] using hc
  have hbalance : 2 * (tail.sum - t) +
      3 * ons_cyclicTurnSum dirs = 0 := by
    rw [hcyc]
    linear_combination hopen + hclosing'
  have hside' : (t = 1 → Orientation.leftParity d 0 = 1) ∧
      (t = -1 → Orientation.leftParity d 0 ≠ 1) := by
    simpa only [base, t, tail, h, dirs, d,
      HexCSTerminalSelectedSide] using hside
  rw [hdrop]
  rcases ht with ht | ht
  · left
    refine ⟨ht, ?_⟩
    have hfour := hsign.1 (hside'.1 ht)
    simp only [List.sum_cons, ht] at hbalance ⊢
    omega
  · right
    refine ⟨ht, ?_⟩
    have hnegfour := hsign.2 (hside'.2 ht)
    simp only [List.sum_cons, ht] at hbalance ⊢
    omega


theorem hexCS_cyclicLoopPair_of_terminal_side
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (endEdge : Fin 3) (ts : List ℤ)
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3)
    (hside :
      let base := ts.take C.index
      let t := ts[C.index]'C.index_lt
      let tail := ts.drop (C.index + 1)
      let h := hexInfra_headAccum 1 base
      HexCSTerminalSelectedSide t h tail) :
    ∃ P : HexEndpointCyclicLoopPair
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      ts ∈ P.piece := by
  obtain ⟨P, hmem, _⟩ := hexCS_cyclicLoopPair_of_selected_terminal_cycle
    c endEdge ts C hnotOutside hadm hcount
      (C.selected_terminal_cycle_of_side hnotOutside hadm.1 endEdge
        hadm.2.2 hcount hside)
  exact ⟨P, hmem⟩


theorem hexCS_cyclicLoopPair_of_terminal_with_stem
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (endEdge : Fin 3) (ts : List ℤ)
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    ∃ P : HexEndpointCyclicLoopPair
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      ts ∈ P.piece ∧
        hexInfra_midAccum hexAWStart 1 P.base +
          halfStep (hexInfra_headAccum 1 P.base) = hexAWPos c ∧
        ∀ u ∈ P.piece,
          specialMidCount hexAWStart 1 (hexAWPos c)
            (hexAWMid c 0 - hexAWPos c) u = 3 := by
  apply hexCS_cyclicLoopPair_of_selected_terminal_cycle
    c endEdge ts C hnotOutside hadm hcount
  apply C.selected_terminal_cycle_of_side
    hnotOutside hadm.1 endEdge hadm.2.2 hcount
  exact C.terminal_selected_side hnotOutside endEdge hadm hcount


theorem hexCS_cyclicLoopPair_of_terminal
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (endEdge : Fin 3) (ts : List ℤ)
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    ∃ P : HexEndpointCyclicLoopPair
        (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      ts ∈ P.piece := by
  obtain ⟨P, hmem, _⟩ := hexCS_cyclicLoopPair_of_terminal_with_stem
    c endEdge ts C hnotOutside hadm hcount
  exact ⟨P, hmem⟩

theorem hexCS_cyclicSucc_ne_pred (j : Fin 3) :
    hexCyclicSucc j ≠ hexCyclicPred j := by
  fin_cases j <;> decide

theorem hexCS_cyclicPair_members_ne
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0)
    (P : HexEndpointCyclicLoopPair region a h0 v du) :
    P.base ++ P.loopQ ≠
      P.base ++ hexEndpointLoopPartner P.loopQ := by
  intro heq
  have hm : labelMid v du (hexCyclicSucc P.baseLabel) =
      labelMid v du (hexCyclicPred P.baseLabel) :=
    P.succ_valid.2.2.symm.trans (heq ▸ P.pred_valid.2.2)
  exact hexCS_cyclicSucc_ne_pred P.baseLabel
    (labelMid_injective hdu hm)


theorem hexCS_cyclicPair_piece_eq_of_overlap
    {region : ℂ → Prop} {c : HexAWCoord} {du : ℂ}
    (hdu : du ≠ 0)
    (P Q : HexEndpointCyclicLoopPair region hexAWStart 1
      (hexAWPos c) du)
    (hPstem : hexInfra_midAccum hexAWStart 1 P.base +
      halfStep (hexInfra_headAccum 1 P.base) = hexAWPos c)
    (hQstem : hexInfra_midAccum hexAWStart 1 Q.base +
      halfStep (hexInfra_headAccum 1 Q.base) = hexAWPos c)
    (z : List ℤ) (hzP : z ∈ P.piece) (hzQ : z ∈ Q.piece) :
    P.piece = Q.piece := by
  have hpCases : z = P.base ++ P.loopQ ∨
      z = P.base ++ hexEndpointLoopPartner P.loopQ := by
    simpa only [HexEndpointCyclicLoopPair.piece, Finset.mem_insert,
      Finset.mem_singleton] using hzP
  have hqCases : z = Q.base ++ Q.loopQ ∨
      z = Q.base ++ hexEndpointLoopPartner Q.loopQ := by
    simpa only [HexEndpointCyclicLoopPair.piece, Finset.mem_insert,
      Finset.mem_singleton] using hzQ
  obtain ⟨ptail, hpLoop⟩ := P.loopQ_first
  obtain ⟨qtail, hqLoop⟩ := Q.loopQ_first
  have hpLt : P.base.length < z.length := by
    rcases hpCases with hp | hp <;> rw [hp, hpLoop] <;>
      simp [hexEndpointLoopPartner]
  have hqLt : Q.base.length < z.length := by
    rcases hqCases with hq | hq <;> rw [hq, hqLoop] <;>
      simp [hexEndpointLoopPartner]
  have hpPos : hexJordan_vertexPos hexAWStart 1 z P.base.length =
      hexAWPos c := by
    rcases hpCases with hp | hp <;> rw [hp] <;>
      simpa [hexJordan_vertexPos] using hPstem
  have hqPos : hexJordan_vertexPos hexAWStart 1 z Q.base.length =
      hexAWPos c := by
    rcases hqCases with hq | hq <;> rw [hq] <;>
      simpa [hexJordan_vertexPos] using hQstem
  have hzSaw : (ofTurns hexAWStart 1 z).EndpointIsSAW := by
    rcases hpCases with hp | hp
    · rw [hp]
      exact P.succ_valid.1.2
    · rw [hp]
      exact P.pred_valid.1.2
  have hlen : P.base.length = Q.base.length := by
    by_contra hne
    exact (hexEndpoint_vertexPos_ne_of_saw z hzSaw
      P.base.length Q.base.length hpLt hqLt hne)
        (hpPos.trans hqPos.symm)
  have hpTake : z.take P.base.length = P.base := by
    rcases hpCases with hp | hp <;> rw [hp] <;> simp
  have hqTake : z.take Q.base.length = Q.base := by
    rcases hqCases with hq | hq <;> rw [hq] <;> simp
  have hbase : P.base = Q.base := by
    calc
      P.base = z.take P.base.length := hpTake.symm
      _ = z.take Q.base.length := by rw [hlen]
      _ = Q.base := hqTake
  have hpDrop : z.drop P.base.length = P.loopQ ∨
      z.drop P.base.length = hexEndpointLoopPartner P.loopQ := by
    rcases hpCases with hp | hp
    · left
      rw [hp]
      simp
    · right
      rw [hp]
      simp
  have hqDrop : z.drop Q.base.length = Q.loopQ ∨
      z.drop Q.base.length = hexEndpointLoopPartner Q.loopQ := by
    rcases hqCases with hq | hq
    · left
      rw [hq]
      simp
    · right
      rw [hq]
      simp
  have hloop : P.loopQ = Q.loopQ := by
    rcases hpDrop with hp | hp <;> rcases hqDrop with hq | hq
    · exact hp.symm.trans (hlen ▸ hq)
    · have hcross : P.loopQ = hexEndpointLoopPartner Q.loopQ :=
        hp.symm.trans (hlen ▸ hq)
      rw [hpLoop, hqLoop] at hcross
      simp [hexEndpointLoopPartner] at hcross
    · have hcross : hexEndpointLoopPartner P.loopQ = Q.loopQ :=
        hp.symm.trans (hlen ▸ hq)
      rw [hpLoop, hqLoop] at hcross
      simp [hexEndpointLoopPartner] at hcross
    · have heq : hexEndpointLoopPartner P.loopQ =
          hexEndpointLoopPartner Q.loopQ := hp.symm.trans (hlen ▸ hq)
      have := congrArg hexEndpointLoopPartner heq
      simpa using this
  simp only [HexEndpointCyclicLoopPair.piece, hbase, hloop]

theorem hexCS_vertex_ne_outside_start
    {T L : ℕ} (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    c ≠ hexAWNeighbor hexAWOriginCoord 0 := by
  intro heq
  rw [heq, hexCS_mem_vertexSet_iff] at hc
  simp [hexAWOriginCoord, hexAWNeighbor, hexCSInStrip,
    hexAWBookRe2, hexAWDepth, hexAWLong] at hc

theorem hexCS_vertex_mid_mem_region
    {T L : ℕ} {hT : 0 < T}
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (e : Fin 3) :
    (hexCSFiniteRegion T L hT).inRegion (hexAWMid c e) := by
  change hexAWMid c e ∈ hexCSMids T L
  rw [hexCSMids, Finset.mem_biUnion]
  refine ⟨⟨c, hc⟩, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨e, Finset.mem_univ _, rfl⟩


end
end StatMech.Universality
