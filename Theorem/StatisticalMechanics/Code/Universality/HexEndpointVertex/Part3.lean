/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem hexAW_two_mul_mid_eq_returnMidSum (c : HexAWCoord) (e : Fin 3) :
    (2 : ℂ) * hexAWMid c e =
      (hexAWReturnMidSum c e).value * hexUnit 1 := by
  calc
    (2 : ℂ) * hexAWMid c e =
        hexAWPos c + hexAWPos (hexAWNeighbor c e) := by
          unfold hexAWMid
          ring
    _ = (hexAWReturnPos c).value * hexUnit 1 +
        (hexAWReturnPos (hexAWNeighbor c e)).value * hexUnit 1 := by
          rw [← hexAWPos_eq_returnPos_mul,
            ← hexAWPos_eq_returnPos_mul]
    _ = (hexAWReturnMidSum c e).value * hexUnit 1 := by
          rw [hexAWReturnMidSum, HexReturnCoord.value_add]
          ring


theorem HexReturnCoord.value_injective :
    Function.Injective HexReturnCoord.value := by
  intro d e h
  let q : HexReturnCoord := ⟨d.x - e.x, d.y - e.y⟩
  have hq : q.value = 0 := by
    rw [show q.value = d.value - e.value by
      simp [q, HexReturnCoord.value]
      ring, h, sub_self]
  have hzero := hexReturnCoord_value_eq_zero hq
  rcases d with ⟨dx, dy⟩
  rcases e with ⟨ex, ey⟩
  simp only [q, HexReturnCoord.zero, HexReturnCoord.mk.injEq] at hzero ⊢
  omega


theorem hexAWPos_injective : Function.Injective hexAWPos := by
  intro c d hpos
  have hvalue : (hexAWReturnPos c).value * hexUnit 1 =
      (hexAWReturnPos d).value * hexUnit 1 := by
    rw [← hexAWPos_eq_returnPos_mul,
      ← hexAWPos_eq_returnPos_mul, hpos]
  have hcoord : hexAWReturnPos c = hexAWReturnPos d := by
    apply HexReturnCoord.value_injective
    exact mul_right_cancel₀ (hexUnit_ne_zero 1) hvalue
  rcases c with ⟨i, j, color⟩
  rcases d with ⟨i', j', color'⟩
  cases color <;> cases color'
  all_goals
    simp [hexAWReturnPos, HexReturnCoord.mk.injEq] at hcoord ⊢
  all_goals omega


theorem hexAWMid_eq_iff (c d : HexAWCoord) (e f : Fin 3) :
    hexAWMid c e = hexAWMid d f ↔
      (d = c ∧ f = e) ∨ (d = hexAWNeighbor c e ∧ f = e) := by
  constructor
  · intro hmid
    have hvalue : (hexAWReturnMidSum c e).value * hexUnit 1 =
        (hexAWReturnMidSum d f).value * hexUnit 1 := by
      rw [← hexAW_two_mul_mid_eq_returnMidSum,
        ← hexAW_two_mul_mid_eq_returnMidSum, hmid]
    have hcoord : hexAWReturnMidSum c e = hexAWReturnMidSum d f := by
      apply HexReturnCoord.value_injective
      exact mul_right_cancel₀ (hexUnit_ne_zero 1) hvalue
    rcases c with ⟨i, j, color⟩
    rcases d with ⟨i', j', color'⟩
    cases color <;> cases color' <;> fin_cases e <;> fin_cases f
    all_goals
      simp [hexAWReturnMidSum, hexAWReturnPos, hexAWNeighbor,
        HexReturnCoord.add, HexReturnCoord.mk.injEq] at hcoord ⊢
    all_goals omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · simp


theorem hexEndpoint_vertex_eq_runPos (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      (hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos.value * hexUnit 1 := by
  have hbase : halfStep 1 =
      HexReturnCoord.base.value * halfStep 1 := by simp
  have hgeom := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base hexAWStart (halfStep 1) 1 ts hbase hlegal).1
  have hstart : hexAWStart + halfStep 1 = 0 := by
    unfold hexAWStart halfStep
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring
  have hscale : (2 : ℂ) * halfStep 1 = hexUnit 1 := by
    unfold halfStep
    ring
  rw [hgeom]
  simp only [HexReturnCoord.value_zero, sub_zero]
  rw [show hexAWStart + halfStep 1 +
      2 * ((hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos.value * halfStep 1) =
      (hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos.value * ((2 : ℂ) * halfStep 1) by
        rw [hstart, zero_add]
        ring,
    hscale]


theorem hexEndpointCoordRun_pos_exists_aw (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∃ c : HexAWCoord,
      (hexEndpointCoordRun HexReturnCoord.zero
        HexReturnCoord.base ts).pos = hexAWReturnPos c := by
  let run := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts
  have hc := hexEndpointCoordRun_compatible HexReturnCoord.zero
    HexReturnCoord.base ts hexEndpointCoordRun_base_compatible
      HexReturnCoord.base_isUnit hlegal
  rcases hc with ⟨_, ⟨k, hk⟩⟩ | ⟨_, ⟨k, hk⟩⟩
  · refine ⟨⟨run.pos.y - k, -k, .black⟩, ?_⟩
    rcases hp : run.pos with ⟨x, y⟩
    simp only [run, hp, hexAWReturnPos, HexReturnCoord.mk.injEq] at hk ⊢
    omega
  · refine ⟨⟨run.pos.y - k, -k, .white⟩, ?_⟩
    rcases hp : run.pos with ⟨x, y⟩
    simp only [run, hp, hexAWReturnPos, HexReturnCoord.mk.injEq] at hk ⊢
    omega


theorem hexEndpoint_vertex_exists_aw (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    ∃ c : HexAWCoord,
      hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) = hexAWPos c := by
  obtain ⟨c, hc⟩ := hexEndpointCoordRun_pos_exists_aw ts hlegal
  refine ⟨c, ?_⟩
  rw [hexEndpoint_vertex_eq_runPos ts hlegal, hc,
    ← hexAWPos_eq_returnPos_mul]


theorem hexEndpointCoordRun_pos_eq_aw
    (ts : List ℤ) (c : HexAWCoord)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hvertex : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
    (hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts).pos =
      hexAWReturnPos c := by
  let run := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts
  have hbase : halfStep 1 =
      HexReturnCoord.base.value * halfStep 1 := by simp
  have hgeom := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base hexAWStart (halfStep 1) 1 ts hbase hlegal).1
  have hstart : hexAWStart + halfStep 1 = 0 := by
    unfold hexAWStart halfStep
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring
  have hscale : (2 : ℂ) * halfStep 1 = hexUnit 1 := by
    unfold halfStep
    ring
  have hrun : run.pos.value * hexUnit 1 =
      (hexAWReturnPos c).value * hexUnit 1 := by
    rw [← hexAWPos_eq_returnPos_mul c, ← hvertex]
    dsimp [run]
    rw [hgeom]
    simp only [HexReturnCoord.value_zero, sub_zero]
    rw [show hexAWStart + halfStep 1 +
        2 * ((hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).pos.value * halfStep 1) =
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).pos.value *
            ((2 : ℂ) * halfStep 1) by rw [hstart, zero_add]; ring,
      hscale]
  have hvalue : run.pos.value = (hexAWReturnPos c).value := by
    exact mul_right_cancel₀ (hexUnit_ne_zero 1) hrun
  exact HexReturnCoord.value_injective hvalue


theorem hexEndpointCoordRun_dir_color_aw
    (ts : List ℤ) (c : HexAWCoord)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hvertex : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
    match c.color with
    | .black =>
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).dir.IsEvenDir
    | .white =>
        (hexEndpointCoordRun HexReturnCoord.zero
          HexReturnCoord.base ts).dir.IsOddDir := by
  have hc := hexEndpointCoordRun_compatible HexReturnCoord.zero
    HexReturnCoord.base ts hexEndpointCoordRun_base_compatible
      HexReturnCoord.base_isUnit hlegal
  have hp := hexEndpointCoordRun_pos_eq_aw ts c hlegal hvertex
  unfold HexEndpointCoordRun.ColorCompatible at hc
  rw [hp] at hc
  rcases c with ⟨i, j, color⟩
  cases color
  · rcases hc with hc | hc
    · exact hc.1
    · rcases hc.2 with ⟨k, hk⟩
      simp [hexAWReturnPos] at hk
      omega
  · rcases hc with hc | hc
    · rcases hc.2 with ⟨k, hk⟩
      simp [hexAWReturnPos] at hk
      omega
    · exact hc.1


theorem hexEndpoint_mid_incident_aw
    (ts : List ℤ) (c : HexAWCoord)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hvertex : hexInfra_midAccum hexAWStart 1 ts +
      halfStep (hexInfra_headAccum 1 ts) = hexAWPos c) :
    ∃ e : Fin 3,
      hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
  let run := hexEndpointCoordRun HexReturnCoord.zero HexReturnCoord.base ts
  have hbase : halfStep 1 =
      HexReturnCoord.base.value * halfStep 1 := by simp
  have hdir := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base hexAWStart (halfStep 1) 1 ts hbase hlegal).2
  have hmid : hexInfra_midAccum hexAWStart 1 ts =
      hexAWPos c - run.dir.value * halfStep 1 := by
    dsimp [run]
    linear_combination hvertex - hdir
  have finish (e : Fin 3)
      (hvec : -(run.dir.value * halfStep 1) =
        halfStep (hexAWHeading c e)) :
      hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
    have haw := hexAWMid_sub_pos_eq_halfStep c e
    calc
      hexInfra_midAccum hexAWStart 1 ts =
          hexAWPos c + halfStep (hexAWHeading c e) := by
            rw [hmid, ← hvec]
            ring
      _ = hexAWMid c e := by linear_combination -haw
  have hd := hexEndpointCoordRun_dir_color_aw ts c hlegal hvertex
  rcases c with ⟨i, j, color⟩
  cases color
  · rcases hd with hd | hd | hd
    · refine ⟨0, finish 0 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_one, Int.cast_zero,
        zero_mul, add_zero, one_mul, hexAWHeading]
      simpa using (hexEndpoint_halfStep_add_three 1).symm
    · refine ⟨1, finish 1 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_zero, Int.cast_one,
        zero_add, one_mul, hexAWHeading]
      simpa using (hexEndpoint_halfStep_sub_one 1).symm
    · refine ⟨2, finish 2 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_neg, Int.cast_one,
        neg_mul, hexAWHeading]
      have hv : (-1 : ℂ) + -(1 * hexOmega) = hexOmega ^ 2 := by
        rw [hexConcrete_omega_cubic]
        ring
      rw [hv]
      simpa using (hexEndpoint_halfStep_add_one 1).symm
  · rcases hd with hd | hd | hd
    · refine ⟨2, finish 2 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_one, one_mul, hexAWHeading]
      rw [show (5 : ℤ) = 1 + 4 by norm_num,
        hexEndpoint_halfStep_add_four, hexConcrete_omega_cubic]
      ring
    · refine ⟨0, finish 0 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_neg, Int.cast_one,
        Int.cast_zero, zero_mul, add_zero, neg_mul, one_mul, hexAWHeading]
      rw [show (7 : ℤ) = 1 + 6 by norm_num,
        hexEndpoint_halfStep_add_six]
      ring
    · refine ⟨1, finish 1 ?_⟩
      rw [hd]
      simp only [HexReturnCoord.value, Int.cast_zero, zero_add,
        Int.cast_neg, Int.cast_one, neg_mul, one_mul, hexAWHeading]
      simpa using (hexEndpoint_halfStep_add_two 1).symm


theorem hexEndpoint_forward_vertex_of_mid
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e) :
    hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) = hexAWPos c ∨
      hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
        hexAWPos (hexAWNeighbor c e) := by
  obtain ⟨d, hvertex⟩ := hexEndpoint_vertex_exists_aw ts hlegal
  obtain ⟨f, hinc⟩ := hexEndpoint_mid_incident_aw ts d hlegal hvertex
  have hedge : hexAWMid c e = hexAWMid d f := hmid.symm.trans hinc
  rcases (hexAWMid_eq_iff c d e f).mp hedge with
      ⟨hd, _⟩ | ⟨hd, _⟩
  · left
    simpa [hd] using hvertex
  · right
    simpa [hd] using hvertex


theorem hexEndpoint_next_mid_of_forward_vertex
    (s : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ u ∈ s, u = 1 ∨ u = -1)
    (ht : t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 s = hexAWMid c e)
    (hforward : hexInfra_midAccum hexAWStart 1 s +
      halfStep (hexInfra_headAccum 1 s) = hexAWPos c) :
    ∃ f : Fin 3, f ≠ e ∧
      hexInfra_midAccum hexAWStart 1 (s ++ [t]) = hexAWMid c f := by
  have hlegal' : ∀ u ∈ s ++ [t], u = 1 ∨ u = -1 := by
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hlegal u hu
    · exact ht
  have hnew := hexCyclic_midAccum_append_single hexAWStart 1 t s
  obtain ⟨d, hvertex⟩ := hexEndpoint_vertex_exists_aw (s ++ [t]) hlegal'
  obtain ⟨f, hinc⟩ := hexEndpoint_mid_incident_aw
    (s ++ [t]) d hlegal' hvertex
  have hnew' : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexAWPos c + halfStep (hexInfra_headAccum 1 s + t) := by
    linear_combination hnew + hforward
  have hhead : hexInfra_headAccum 1 (s ++ [t]) =
      hexInfra_headAccum 1 s + t := by
    simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
    ring
  rw [hhead] at hvertex
  have hneighborPos : hexAWPos (hexAWNeighbor d f) = hexAWPos c := by
    unfold hexAWMid at hinc
    linear_combination -2 * hinc + hvertex + hnew'
  have hneighbor : hexAWNeighbor d f = c :=
    hexAWPos_injective hneighborPos
  have hlocal : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexAWMid c f := by
    calc
      hexInfra_midAccum hexAWStart 1 (s ++ [t]) = hexAWMid d f := hinc
      _ = hexAWMid (hexAWNeighbor d f) f := (hexAWMid_neighbor d f).symm
      _ = hexAWMid c f := by rw [hneighbor]
  refine ⟨f, ?_, hlocal⟩
  intro hfe
  have hsame : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexInfra_midAccum hexAWStart 1 s := by
    rw [hlocal, hfe, ← hmid]
  apply hexW1_halfStep_add_ne_zero (hexInfra_headAccum 1 s) t ht
  linear_combination -hnew + hsame


theorem hexEndpoint_previous_mid_of_forward_outer
    (s : List ℤ) (t : ℤ) (c : HexAWCoord) (e : Fin 3)
    (hlegal : ∀ u ∈ s, u = 1 ∨ u = -1)
    (ht : t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexAWMid c e)
    (hforward : hexInfra_midAccum hexAWStart 1 (s ++ [t]) +
      halfStep (hexInfra_headAccum 1 (s ++ [t])) =
        hexAWPos (hexAWNeighbor c e)) :
    ∃ f : Fin 3, f ≠ e ∧
      hexInfra_midAccum hexAWStart 1 s = hexAWMid c f := by
  have hnew := hexCyclic_midAccum_append_single hexAWStart 1 t s
  have hhead : hexInfra_headAccum 1 (s ++ [t]) =
      hexInfra_headAccum 1 s + t := by
    simp [hexInfra_headAccum_eq_add_sum, List.sum_append]
    ring
  rw [hhead] at hforward
  have hcurrentBack : hexInfra_midAccum hexAWStart 1 (s ++ [t]) -
      halfStep (hexInfra_headAccum 1 s + t) = hexAWPos c := by
    unfold hexAWMid at hmid
    linear_combination 2 * hmid - hforward
  have hprevious : hexInfra_midAccum hexAWStart 1 s +
      halfStep (hexInfra_headAccum 1 s) = hexAWPos c := by
    linear_combination -hnew + hcurrentBack
  obtain ⟨f, hinc⟩ := hexEndpoint_mid_incident_aw s c hlegal hprevious
  refine ⟨f, ?_, hinc⟩
  intro hfe
  have hsame : hexInfra_midAccum hexAWStart 1 (s ++ [t]) =
      hexInfra_midAccum hexAWStart 1 s := by
    rw [hmid, hinc, hfe]
  apply hexW1_halfStep_add_ne_zero (hexInfra_headAccum 1 s) t ht
  linear_combination -hnew + hsame


theorem hexEndpoint_internal_mid_forces_second
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < ts.length)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hmid : hexInfra_midAccum hexAWStart 1 (ts.take k) =
      hexAWMid c e) :
    ∃ f : Fin 3, f ≠ e ∧
      PassesThrough hexAWStart 1 ts (hexAWMid c f) := by
  have prefixMem (n : ℕ) (hn : n ≤ ts.length) :
      PassesThrough hexAWStart 1 ts
        (hexInfra_midAccum hexAWStart 1 (ts.take n)) := by
    unfold PassesThrough HexWalk.mids
    rw [List.mem_iff_getElem?]
    exact ⟨n, hexJordan_midsAux_getElem?_eq hexAWStart 1 ts n hn⟩
  have hlegalTake : ∀ u ∈ ts.take k, u = 1 ∨ u = -1 := by
    intro u hu
    exact hlegal u (List.mem_of_mem_take hu)
  rcases hexEndpoint_forward_vertex_of_mid (ts.take k) c e
      hlegalTake hmid with hforward | hforward
  · let t := ts[k]
    have ht : t = 1 ∨ t = -1 := hlegal t (List.getElem_mem hklt)
    obtain ⟨f, hfe, hnext⟩ := hexEndpoint_next_mid_of_forward_vertex
      (ts.take k) t c e hlegalTake ht hmid hforward
    refine ⟨f, hfe, ?_⟩
    have htake : ts.take k ++ [t] = ts.take (k + 1) := by
      exact (List.take_succ_eq_append_getElem hklt).symm
    rw [htake] at hnext
    rw [← hnext]
    exact prefixMem (k + 1) (by omega)
  · cases k with
    | zero => omega
    | succ n =>
        let t := ts[n]
        have hnlt : n < ts.length := by omega
        have ht : t = 1 ∨ t = -1 := hlegal t (List.getElem_mem hnlt)
        have htake : ts.take (n + 1) = ts.take n ++ [t] :=
          List.take_succ_eq_append_getElem hnlt
        have hlegalPrev : ∀ u ∈ ts.take n, u = 1 ∨ u = -1 := by
          intro u hu
          exact hlegal u (List.mem_of_mem_take hu)
        rw [htake] at hmid hforward
        obtain ⟨f, hfe, hprev⟩ :=
          hexEndpoint_previous_mid_of_forward_outer
            (ts.take n) t c e hlegalPrev ht hmid hforward
        refine ⟨f, hfe, ?_⟩
        rw [← hprev]
        exact prefixMem n (by omega)


theorem hexEndpoint_return_direction_cases (m : ℂ) (h : ℤ) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (hreturn : hexInfra_midAccum m h ts +
        halfStep (hexInfra_headAccum h ts) = m + halfStep h) :
    halfStep (hexInfra_headAccum h ts) = halfStep h ∨
      halfStep (hexInfra_headAccum h ts) = halfStep (h + 2) ∨
      halfStep (hexInfra_headAccum h ts) = halfStep (h + 4) := by
  have heven := hexEndpoint_return_even_direction m h ts hlegal hreturn
  have hbase : halfStep h = HexReturnCoord.base.value * halfStep h := by simp
  have hgeom := (hexEndpointCoordRun_geometry HexReturnCoord.zero
    HexReturnCoord.base m (halfStep h) h ts hbase hlegal).2
  rcases heven with hd | hd | hd
  · left
    rw [hgeom, hd]
    simp [HexReturnCoord.value]
  · right
    left
    have hv : (HexReturnCoord.mk 0 1).value = hexOmega := by
      simp [HexReturnCoord.value]
    rw [hgeom, hd, hv, hexEndpoint_halfStep_add_two]
  · right
    right
    have hv : (HexReturnCoord.mk (-1) (-1)).value = hexOmega ^ 2 := by
      simp [HexReturnCoord.value]
      rw [hexConcrete_omega_cubic]
      ring
    rw [hgeom, hd, hv, hexEndpoint_halfStep_add_four]


theorem hexEndpoint_repeated_lookahead_direction
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).LegalTurns)
    (hrepeat : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) ∈
      (ofTurns a h0 ts).endpointVertices) :
    ∃ k : ℕ, k < ts.length ∧
      hexJordan_vertexPos a h0 ts k =
        hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) ∧
      (let hk := hexInfra_headAccum h0 (ts.take k)
       halfStep (hexInfra_headAccum h0 ts) = halfStep hk ∨
        halfStep (hexInfra_headAccum h0 ts) = halfStep (hk + 2) ∨
        halfStep (hexInfra_headAccum h0 ts) = halfStep (hk + 4)) := by
  rw [List.mem_iff_getElem] at hrepeat
  obtain ⟨k, hklen, hkget⟩ := hrepeat
  have hkts : k < ts.length := by
    simpa [endpointNumVertices] using hklen
  have hkfull : k < (verticesAux a h0 ts).length := by
    rw [length_verticesAux]
    omega
  have hkdrop : k < (verticesAux a h0 ts).dropLast.length := by
    simpa [endpointVertices, vertices, ofTurns] using hklen
  have hkgetDrop : (verticesAux a h0 ts).dropLast[k] =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    simpa [endpointVertices, vertices, ofTurns] using hkget
  have hkget' : (verticesAux a h0 ts)[k] =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    exact (List.getElem_dropLast hkdrop).symm.trans hkgetDrop
  have hpos := hexJordan_verticesAux_getElem?_eq a h0 ts k (le_of_lt hkts)
  rw [List.getElem?_eq_getElem hkfull, Option.some.injEq] at hpos
  let m' := hexInfra_midAccum a h0 (ts.take k)
  let h' := hexInfra_headAccum h0 (ts.take k)
  let us := ts.drop k
  have hsplit : ts.take k ++ us = ts := by
    dsimp [us]
    exact List.take_append_drop k ts
  have hlegalDrop : ∀ t ∈ us, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (by
      apply List.mem_of_mem_drop at ht
      simpa [us] using ht)
  have hmid : hexInfra_midAccum m' h' us = hexInfra_midAccum a h0 ts := by
    dsimp [m', h']
    rw [← hexJordan_midAccum_append, hsplit]
  have hhead : hexInfra_headAccum h' us = hexInfra_headAccum h0 ts := by
    dsimp [h']
    rw [← hexJordan_headAccum_append, hsplit]
  have hfirst : m' + halfStep h' =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    dsimp [m', h']
    exact hpos.symm.trans hkget'
  have hreturn : hexInfra_midAccum m' h' us +
      halfStep (hexInfra_headAccum h' us) = m' + halfStep h' := by
    rw [hmid, hhead, hfirst]
  refine ⟨k, hkts, ?_, ?_⟩
  unfold hexJordan_vertexPos
  exact hpos.symm.trans hkget'
  have hc := hexEndpoint_return_direction_cases m' h' us hlegalDrop hreturn
  rw [hhead] at hc
  simpa [h'] using hc


theorem hexEndpoint_prefix_mid_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (k : ℕ) (hk : k ≤ ts.length) :
    PassesThrough a h0 ts (hexInfra_midAccum a h0 (ts.take k)) := by
  unfold PassesThrough HexWalk.mids
  rw [List.mem_iff_getElem?]
  exact ⟨k, hexJordan_midsAux_getElem?_eq a h0 ts k hk⟩


theorem hexEndpoint_previous_mid_is_label (v du m : ℂ) (j : Fin 3)
    (h H : ℤ)
    (hm : m + halfStep h = v)
    (hj : labelMid v du j + halfStep H = v)
    (horbit : halfStep H = halfStep h ∨
      halfStep H = halfStep (h + 2) ∨
      halfStep H = halfStep (h + 4)) :
    ∃ l : Fin 3, m = labelMid v du l := by
  have hcube : hexOmega ^ 3 = (1 : ℂ) := hexOmega_primRoot.pow_eq_one
  rcases horbit with hsame | htwo | hfour
  · refine ⟨j, ?_⟩
    linear_combination hm - hj + hsame
  · refine ⟨hexCyclicPred j, ?_⟩
    rw [hexCyclicPred_mid]
    rw [hexEndpoint_halfStep_add_two] at htwo
    have hoff : labelMid v du j - v = -halfStep H := by
      linear_combination hj
    rw [hoff, htwo]
    have hprod : hexOmega ^ 2 * -(hexOmega * halfStep h) = -halfStep h := by
      rw [show hexOmega ^ 2 * -(hexOmega * halfStep h) =
        -(hexOmega ^ 3 * halfStep h) by ring, hcube, one_mul]
    rw [hprod]
    linear_combination hm
  · refine ⟨hexCyclicSucc j, ?_⟩
    rw [hexCyclicSucc_mid]
    rw [hexEndpoint_halfStep_add_four] at hfour
    have hoff : labelMid v du j - v = -halfStep H := by
      linear_combination hj
    rw [hoff, hfour]
    have hprod : hexOmega * -(hexOmega ^ 2 * halfStep h) = -halfStep h := by
      rw [show hexOmega * -(hexOmega ^ 2 * halfStep h) =
        -(hexOmega ^ 3 * halfStep h) by ring, hcube, one_mul]
    rw [hprod]
    linear_combination hm

theorem hexCyclicSucc_ne_self (j : Fin 3) : hexCyclicSucc j ≠ j := by
  fin_cases j <;> decide

theorem hexCyclicPred_ne_self (j : Fin 3) : hexCyclicPred j ≠ j := by
  fin_cases j <;> decide


theorem hexEndpoint_next_mid_is_distinct_label (v du m : ℂ) (j : Fin 3)
    (h t : ℤ)
    (hm : m = labelMid v du j)
    (hv : m + halfStep h = v)
    (ht : t = 1 ∨ t = -1) :
    ∃ l : Fin 3, l ≠ j ∧
      m + halfStep h + halfStep (h + t) = labelMid v du l := by
  rcases ht with rfl | rfl
  · refine ⟨hexCyclicPred j, hexCyclicPred_ne_self j, ?_⟩
    rw [hexCyclicPred_mid, ← hm, hexEndpoint_halfStep_add_one]
    linear_combination (1 - hexOmega ^ 2) * hv
  · refine ⟨hexCyclicSucc j, hexCyclicSucc_ne_self j, ?_⟩
    rw [show h + (-1 : ℤ) = h - 1 by ring, hexCyclicSucc_mid,
      ← hm, hexEndpoint_halfStep_sub_one]
    linear_combination (1 - hexOmega) * hv


theorem specialMidCount_ge_two_of_labels (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ) (j l : Fin 3) (hjl : j ≠ l)
    (hj : PassesThrough a h0 ts (labelMid v du j))
    (hl : PassesThrough a h0 ts (labelMid v du l)) :
    2 ≤ specialMidCount a h0 v du ts := by
  fin_cases j <;> fin_cases l <;>
    simp_all [specialMidCount, labelMid]


theorem hexEndpoint_count_ge_two_of_lookahead_mem
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3) (ts : List ℤ)
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).LegalTurns)
    (hmem : v ∈ (ofTurns a h0 ts).endpointVertices) :
    2 ≤ specialMidCount a h0 v du ts := by
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  have hlook : hexInfra_midAccum a h0 ts +
      halfStep (hexInfra_headAccum h0 ts) = v := by
    rw [hend]
    exact L.lastVertex
  have hrep : hexInfra_midAccum a h0 ts +
      halfStep (hexInfra_headAccum h0 ts) ∈
        (ofTurns a h0 ts).endpointVertices := by
    simpa [hlook] using hmem
  obtain ⟨k, hk, hpos, horbit⟩ :=
    hexEndpoint_repeated_lookahead_direction a h0 ts hlegal hrep
  let m := hexInfra_midAccum a h0 (ts.take k)
  let h := hexInfra_headAccum h0 (ts.take k)
  let t := ts[k]
  have hmh : m + halfStep h = v := by
    have := hpos
    rw [hlook] at this
    simpa [m, h, hexJordan_vertexPos] using this
  obtain ⟨l, hml⟩ := hexEndpoint_previous_mid_is_label v du m j h
    (hexInfra_headAccum h0 ts) hmh L.lastVertex (by simpa [h] using horbit)
  have ht : t = 1 ∨ t = -1 := hlegal t (List.getElem_mem hk)
  obtain ⟨l', hne, hnext⟩ :=
    hexEndpoint_next_mid_is_distinct_label v du m l h t hml hmh ht
  have hmMem : PassesThrough a h0 ts (labelMid v du l) := by
    rw [← hml]
    exact hexEndpoint_prefix_mid_mem a h0 ts k (le_of_lt hk)
  have hnextAccum :
      hexInfra_midAccum a h0 (ts.take (k + 1)) =
        m + halfStep h + halfStep (h + t) := by
    rw [List.take_succ_eq_append_getElem hk,
      hexCyclic_midAccum_append_single]
  have hnextMem : PassesThrough a h0 ts (labelMid v du l') := by
    rw [← hnext, ← hnextAccum]
    exact hexEndpoint_prefix_mid_mem a h0 ts (k + 1) (by omega)
  exact specialMidCount_ge_two_of_labels a h0 v du ts l l' hne.symm
    hmMem hnextMem


theorem hexEndpoint_vertices_eq_append_lookahead
    (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 ts).vertices =
      (ofTurns a h0 ts).endpointVertices ++
        [hexInfra_midAccum a h0 ts +
          halfStep (hexInfra_headAccum h0 ts)] := by
  let l := verticesAux a h0 ts
  have hn : l ≠ [] := hexInfra_verticesAux_ne_nil a h0 ts
  have hlast : l.getLast hn =
      hexInfra_midAccum a h0 ts + halfStep (hexInfra_headAccum h0 ts) := by
    have hopt := hexInfra_verticesAux_getLast? a h0 ts
    rw [List.getLast?_eq_some_getLast hn] at hopt
    exact Option.some.inj hopt
  change l = l.dropLast ++ [_]
  rw [← hlast]
  exact (List.dropLast_append_getLast hn).symm


theorem hexEndpoint_isSAW_of_lookahead_fresh
    (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).EndpointIsSAW)
    (hfresh : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) ∉
      (ofTurns a h0 ts).endpointVertices) :
    (ofTurns a h0 ts).IsSAW := by
  unfold HexWalk.IsSAW
  rw [hexEndpoint_vertices_eq_append_lookahead]
  rw [List.nodup_append]
  refine ⟨hsaw, by simp, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst y
  exact fun hxy => hfresh (hxy ▸ hx)


theorem hexEndpoint_full_legal_of_count_one
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3) (ts : List ℤ)
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW)
    (hcount : specialMidCount a h0 v du ts = 1) :
    (ofTurns a h0 ts).IsLegalSAW := by
  refine ⟨hlegal.1, hexEndpoint_isSAW_of_lookahead_fresh a h0 ts
    hlegal.2 ?_⟩
  intro hmem
  have hend : hexInfra_midAccum a h0 ts = labelMid v du j := by
    rw [← hexInfra_endMid_eq_midAccum]
    exact L.endsAt
  have hlook : hexInfra_midAccum a h0 ts +
      halfStep (hexInfra_headAccum h0 ts) = v := by
    rw [hend]
    exact L.lastVertex
  have htwo := hexEndpoint_count_ge_two_of_lookahead_mem
    a h0 v du j ts L hlegal.1 (hlook ▸ hmem)
  omega


theorem HexCyclicLaunch.extension_counts_of_one
    {a : ℂ} {h0 : ℤ} {v du : ℂ} {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hdu : du ≠ 0)
    (hcount : specialMidCount a h0 v du ts = 1) :
    specialMidCount a h0 v du (ts ++ [-1]) = 2 ∧
      specialMidCount a h0 v du (ts ++ [1]) = 2 := by
  classical
  have hsuccMids : (ofTurns a h0 (ts ++ [-1])).mids =
      (ofTurns a h0 ts).mids ++
        [labelMid v du (hexCyclicSucc j)] := by
    change midsAux a h0 (ts ++ [-1]) =
      midsAux a h0 ts ++ [labelMid v du (hexCyclicSucc j)]
    have hnew : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + (-1)) =
        labelMid v du (hexCyclicSucc j) := by
      simpa [hexCyclicNewMid] using L.succ_newMid
    rw [hexCyclic_midsAux_append_single, hnew]
  have hpredMids : (ofTurns a h0 (ts ++ [1])).mids =
      (ofTurns a h0 ts).mids ++
        [labelMid v du (hexCyclicPred j)] := by
    change midsAux a h0 (ts ++ [1]) =
      midsAux a h0 ts ++ [labelMid v du (hexCyclicPred j)]
    have hnew : hexInfra_midAccum a h0 ts +
        halfStep (hexInfra_headAccum h0 ts) +
        halfStep (hexInfra_headAccum h0 ts + 1) =
        labelMid v du (hexCyclicPred j) := by
      simpa [hexCyclicNewMid] using L.pred_newMid
    rw [hexCyclic_midsAux_append_single, hnew]
  have hjpass : PassesThrough a h0 ts (labelMid v du j) :=
    hexClass_endsAt_passesThrough ts (labelMid v du j) L.endsAt
  have hpq := hexMid_p_ne_q (v := v) hdu
  have hpr := hexMid_p_ne_r (v := v) hdu
  have hqr := hexMid_q_ne_r (v := v) hdu
  have hrq : hexOmega ^ 2 ≠ hexOmega := Ne.symm hexOmega_ne_sq
  fin_cases j
  all_goals
    simp only [specialMidCount, PassesThrough] at hcount hjpass ⊢
    simp only [hsuccMids, hpredMids, List.mem_append,
      List.mem_singleton] at *
    simp only [labelMid, hexCyclicSucc, hexCyclicPred] at *
    by_cases hp : v + du ∈ (ofTurns a h0 ts).mids
    all_goals by_cases hq : v + hexOmega * du ∈ (ofTurns a h0 ts).mids
    all_goals by_cases hr : v + hexOmega ^ 2 * du ∈ (ofTurns a h0 ts).mids
    all_goals simp_all


theorem hexEndpoint_erase_last_launch
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3)
    (base : List ℤ) (t : ℤ)
    (ht : t = 1 ∨ t = -1)
    (hlast : hexInfra_midAccum a h0 base +
      halfStep (hexInfra_headAccum h0 base) = v)
    (hend : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j)) :
    ∃ l : Fin 3, l ≠ j ∧ HexCyclicLaunch a h0 v du l base := by
  have hnew : hexInfra_midAccum a h0 base +
      halfStep (hexInfra_headAccum h0 base) +
      halfStep (hexInfra_headAccum h0 base + t) = labelMid v du j := by
    unfold HexWalk.EndsAt at hend
    rw [hexInfra_endMid_eq_midAccum,
      hexCyclic_midAccum_append_single] at hend
    exact hend
  have hcube : hexOmega ^ 3 = (1 : ℂ) := hexOmega_primRoot.pow_eq_one
  rcases ht with rfl | rfl
  · refine ⟨hexCyclicSucc j, hexCyclicSucc_ne_self j, ?_⟩
    rw [show hexInfra_headAccum h0 base + (1 : ℤ) =
      hexInfra_headAccum h0 base + 1 by rfl,
      hexEndpoint_halfStep_add_one] at hnew
    have hoff : labelMid v du j - v =
        -(hexOmega ^ 2 * halfStep (hexInfra_headAccum h0 base)) := by
      linear_combination -hnew + hlast
    have hprod : hexOmega * -(hexOmega ^ 2 *
        halfStep (hexInfra_headAccum h0 base)) =
        -halfStep (hexInfra_headAccum h0 base) := by
      rw [show hexOmega * -(hexOmega ^ 2 *
        halfStep (hexInfra_headAccum h0 base)) =
        -(hexOmega ^ 3 * halfStep (hexInfra_headAccum h0 base)) by ring,
        hcube, one_mul]
    have hbaseMid : hexInfra_midAccum a h0 base =
        labelMid v du (hexCyclicSucc j) := by
      rw [hexCyclicSucc_mid, hoff, hprod]
      simpa [sub_eq_add_neg] using (eq_sub_of_add_eq hlast)
    constructor
    · unfold HexWalk.EndsAt
      rw [hexInfra_endMid_eq_midAccum, hbaseMid]
    · rw [← hbaseMid]
      exact hlast
  · refine ⟨hexCyclicPred j, hexCyclicPred_ne_self j, ?_⟩
    rw [show hexInfra_headAccum h0 base + (-1 : ℤ) =
      hexInfra_headAccum h0 base - 1 by ring,
      hexEndpoint_halfStep_sub_one] at hnew
    have hoff : labelMid v du j - v =
        -(hexOmega * halfStep (hexInfra_headAccum h0 base)) := by
      linear_combination -hnew + hlast
    have hprod : hexOmega ^ 2 * -(hexOmega *
        halfStep (hexInfra_headAccum h0 base)) =
        -halfStep (hexInfra_headAccum h0 base) := by
      rw [show hexOmega ^ 2 * -(hexOmega *
        halfStep (hexInfra_headAccum h0 base)) =
        -(hexOmega ^ 3 * halfStep (hexInfra_headAccum h0 base)) by ring,
        hcube, one_mul]
    have hbaseMid : hexInfra_midAccum a h0 base =
        labelMid v du (hexCyclicPred j) := by
      rw [hexCyclicPred_mid, hoff, hprod]
      simpa [sub_eq_add_neg] using (eq_sub_of_add_eq hlast)
    constructor
    · unfold HexWalk.EndsAt
      rw [hexInfra_endMid_eq_midAccum, hbaseMid]
    · rw [← hbaseMid]
      exact hlast


theorem hexEndpoint_base_count_one_of_extension_count_two
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (j : Fin 3)
    (base : List ℤ) (t : ℤ) (hdu : du ≠ 0)
    (hend : (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j))
    (hnew : ¬ PassesThrough a h0 base (labelMid v du j))
    (hcount : specialMidCount a h0 v du (base ++ [t]) = 2) :
    specialMidCount a h0 v du base = 1 := by
  classical
  have hnewMid : hexCyclicNewMid a h0 base t = labelMid v du j := by
    unfold HexWalk.EndsAt at hend
    rw [hexInfra_endMid_eq_midAccum,
      hexCyclic_midAccum_append_single] at hend
    exact hend
  have hmids : (ofTurns a h0 (base ++ [t])).mids =
      (ofTurns a h0 base).mids ++ [labelMid v du j] := by
    change midsAux a h0 (base ++ [t]) =
      midsAux a h0 base ++ [labelMid v du j]
    rw [hexCyclic_midsAux_append_single]
    have : hexInfra_midAccum a h0 base +
        halfStep (hexInfra_headAccum h0 base) +
        halfStep (hexInfra_headAccum h0 base + t) = labelMid v du j := by
      simpa [hexCyclicNewMid] using hnewMid
    rw [this]
  have hpq := hexMid_p_ne_q (v := v) hdu
  have hpr := hexMid_p_ne_r (v := v) hdu
  have hqr := hexMid_q_ne_r (v := v) hdu
  have hrq : hexOmega ^ 2 ≠ hexOmega := Ne.symm hexOmega_ne_sq
  fin_cases j
  all_goals
    simp only [specialMidCount, PassesThrough] at hnew hcount ⊢
    simp only [hmids, List.mem_append, List.mem_singleton] at hcount
    simp only [labelMid] at hnew hcount
    by_cases hp : v + du ∈ (ofTurns a h0 base).mids
    all_goals by_cases hq : v + hexOmega * du ∈ (ofTurns a h0 base).mids
    all_goals by_cases hr : v + hexOmega ^ 2 * du ∈ (ofTurns a h0 base).mids
    all_goals simp_all


end
end StatMech.Universality
