/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

theorem triangularPeriodStateList_isChain {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (r : Nat) :
    List.IsChain
      (fun a b => triangularPeriodStateCoord d b =
        triangularPeriodStateCoord d a + triangularIntStep (d a.2))
      (ons_periodStateList n r) := by
  rw [ons_periodStateList, List.isChain_ofFn]
  intro i hi
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let j : Fin m := ⟨i, by omega⟩
  have hjc : (j.castSucc : Fin (m + 1)) = ⟨i, by omega⟩ := Fin.ext rfl
  have hjs : (j.succ : Fin (m + 1)) = ⟨i + 1, hi⟩ := Fin.ext rfl
  simp only [triangularPeriodStateCoord]
  rw [<- hjc, <- hjs, triangularPeriodicIntPos_succ_cast]
  abel

theorem triangularPeriodState_boundary {m : Nat}
    (d : Fin (m + 1) -> Fin 6) (r : Nat) :
    triangularPeriodStateCoord d (r + 1, 0) =
      triangularPeriodStateCoord d (r, Fin.last m) +
        triangularIntStep (d (Fin.last m)) := by
  simp only [triangularPeriodStateCoord]
  rw [triangularIntPos_zero, zero_add]
  have hdisp : triangularPathDisplacement (List.ofFn d) =
      triangularIntPos d (Fin.last m) +
        triangularIntStep (d (Fin.last m)) := by
    rw [triangularPathDisplacement_ofFn, Fin.sum_univ_castSucc]
    congr 1
    unfold triangularIntPos
    apply Finset.sum_bij (fun i _ => i.castSucc)
    · intro i hi
      simp
    · intro i hi j hj heq
      apply Fin.ext
      exact congrArg (fun x : Fin (m + 1) => x.val) heq
    · intro j hj
      have hjlt : j < Fin.last m := (Finset.mem_filter.mp hj).2
      have hjlast : j ≠ Fin.last m := ne_of_lt hjlt
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hjlast
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · intro i hi
      rfl
  rw [succ_nsmul, hdisp]
  abel

theorem triangularAllPeriodStates_isChain {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) :
    List.IsChain
      (fun a b => triangularPeriodStateCoord d b =
        triangularPeriodStateCoord d a + triangularIntStep (d a.2))
      (ons_allPeriodStates n N) := by
  induction N with
  | zero =>
      simpa [ons_allPeriodStates] using triangularPeriodStateList_isChain d 0
  | succ N ih =>
      rw [ons_allPeriodStates, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      apply List.IsChain.append
        (by simpa [ons_allPeriodStates] using ih)
        (triangularPeriodStateList_isChain d (N + 1))
      intro a ha b hb
      have ha' : a = (N, ons_lastFin n) := by
        change a ∈ (ons_allPeriodStates n N).getLast? at ha
        rw [ons_allPeriodStates_getLast?] at ha
        symm
        simpa using ha
      have hb' : b = (N + 1, (0 : Fin n)) := by
        change b ∈ (ons_periodStateList n (N + 1)).head? at hb
        rw [ons_periodStateList_head?] at hb
        symm
        simpa using hb
      rw [ha', hb']
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      exact triangularPeriodState_boundary d N

theorem triangularPeriodicArcStates_isChain {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (imin imax : Fin n) :
    List.IsChain
      (fun a b => triangularPeriodStateCoord d b =
        triangularPeriodStateCoord d a + triangularIntStep (d a.2))
      (ons_periodicArcStates N imin imax) := by
  exact (triangularAllPeriodStates_isChain d N).drop imin.val |>.take _

theorem triangularPathVertices_map_dropLast_of_chain
    {X : Type*} [Inhabited X]
    (coord : X -> Int × Int) (dir : X -> Fin 6)
    (s : List X) (hs : s ≠ [])
    (hchain : List.IsChain
      (fun a b => coord b = coord a + triangularIntStep (dir a)) s) :
    triangularPathVertices (s.dropLast.map dir) =
      s.map (fun x => coord x - coord s.head!) := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons a as ih =>
      cases as with
      | nil => simp [triangularPathVertices, List.head!]
      | cons b bs =>
          have hc := List.isChain_cons_cons.mp hchain
          have ih' := ih (by simp) hc.2
          rw [List.dropLast_cons_of_ne_nil (by simp), List.map_cons,
            triangularPathVertices_cons, ih']
          simp only [List.map_cons, List.cons.injEq, List.head!,
            sub_self, true_and]
          constructor
          · rw [hc.1]
            abel
          · rw [List.map_map]
            apply List.map_congr_left
            intro x hx
            simp only [Function.comp_apply]
            rw [hc.1]
            abel

theorem triangularPeriodicArc_pathVertices {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPathVertices (triangularPeriodicArcDirections d N imin imax) =
      (ons_periodicArcStates N imin imax).map
        (fun z => triangularPeriodStateCoord d z -
          triangularPeriodStateCoord d (0, imin)) := by
  rw [triangularPeriodicArcDirections]
  have hs : ons_periodicArcStates N imin imax ≠ [] := by
    intro h
    have hh := ons_periodicArcStates_head? N hN imin imax
    rw [h] at hh
    simp at hh
  have h := triangularPathVertices_map_dropLast_of_chain
    (triangularPeriodStateCoord d) (fun z => d z.2)
    (ons_periodicArcStates N imin imax) hs
    (triangularPeriodicArcStates_isChain d N imin imax)
  rw [show (ons_periodicArcStates N imin imax).head! = (0, imin) by
    have hh := ons_periodicArcStates_head? N hN imin imax
    cases hs' : ons_periodicArcStates N imin imax with
    | nil => simp [hs'] at hh
    | cons a as => simpa [hs'] using hh] at h
  exact h

theorem triangularPeriodicArc_pathVertices_nodup {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (triangularPeriodStateCoord d)) :
    (triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax)).Nodup := by
  rw [triangularPeriodicArc_pathVertices d N hN imin imax]
  apply List.Nodup.map (by
    intro a b hab
    apply hinj
    apply sub_left_injective
    exact hab)
  exact ons_periodicArcStates_nodup N imin imax

theorem triangularPeriodicArc_displacement {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPathDisplacement
        (triangularPeriodicArcDirections d N imin imax) =
      triangularPeriodStateCoord d (N, imax) -
        triangularPeriodStateCoord d (0, imin) := by
  have hlast := triangularPathVertices_getLast
    (triangularPeriodicArcDirections d N imin imax)
  rw [triangularPeriodicArc_pathVertices d N hN imin imax,
    List.getLast?_map, ons_periodicArcStates_getLast? N hN] at hlast
  exact Option.some.inj hlast.symm

theorem triangularPeriodicArc_xmin {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmin : ∀ i, (triangularIntPos d imin).1 ≤ (triangularIntPos d i).1)
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax)).dropLast,
      0 ≤ z.1 := by
  intro z hz
  have hz' : z ∈ triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [triangularPeriodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmin s.2
  simp [triangularPeriodStateCoord, Prod.smul_mk]
  nlinarith [Nat.zero_le s.1]

theorem triangularPeriodicArc_xmax {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmax : ∀ i, (triangularIntPos d i).1 ≤ (triangularIntPos d imax).1)
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax)).dropLast,
      z.1 ≤
        (triangularPeriodStateCoord d (N, imax) -
          triangularPeriodStateCoord d (0, imin)).1 := by
  intro z hz
  have hz' : z ∈ triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [triangularPeriodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmax s.2
  have hr := ons_mem_periodicArcStates_fst_le N imin imax s hs
  simp [triangularPeriodStateCoord, Prod.smul_mk]
  nlinarith

theorem triangularExists_path_top (l : List (Fin 6)) (dy : Int) :
    ∃ top : Int, 0 < top ∧ dy < top ∧
      ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top := by
  let ys := ((triangularPathVertices l).dropLast.map
    (fun z => z.2.natAbs)).sum
  let top : Int := (dy.natAbs + ys + 1 : Nat)
  refine ⟨top, ?_, ?_, ?_⟩
  · simp [top]
    positivity
  · have hdy : dy ≤ (dy.natAbs : Int) := Int.le_natAbs
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hys : (0 : Int) ≤ ys := by positivity
    omega
  · intro z hz
    have hmem : z.2.natAbs ∈
        (triangularPathVertices l).dropLast.map (fun w => w.2.natAbs) :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    have hleNat : z.2.natAbs ≤ ys := List.le_sum_of_mem hmem
    have hle : z.2 ≤ (z.2.natAbs : Int) := Int.le_natAbs
    have hcast : (z.2.natAbs : Int) ≤ ys := by exact_mod_cast hleNat
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hdy0 : (0 : Int) ≤ dy.natAbs := by positivity
    omega

theorem triangularPeriodicArc_closure_phase_eq_neg_one
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (triangularPeriodStateCoord d))
    (hmin : ∀ i, (triangularIntPos d imin).1 ≤ (triangularIntPos d i).1)
    (hmax : ∀ i, (triangularIntPos d i).1 ≤ (triangularIntPos d imax).1)
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    let l := triangularPeriodicArcDirections d N imin imax
    let delta := triangularPeriodStateCoord d (N, imax) -
      triangularPeriodStateCoord d (0, imin)
    let top := Classical.choose (triangularExists_path_top l delta.2)
    kwVectorPhaseCycle
      ((l ++ triangularOutsideConnector delta.1 delta.2 top).map
        triangularIntVector) = -1 := by
  dsimp only
  let l := triangularPeriodicArcDirections d N imin imax
  let delta := triangularPeriodStateCoord d (N, imax) -
    triangularPeriodStateCoord d (0, imin)
  let top := Classical.choose (triangularExists_path_top l delta.2)
  have hspec := Classical.choose_spec (triangularExists_path_top l delta.2)
  have htop : 0 < top := hspec.1
  have hdy : delta.2 < top := hspec.2.1
  have hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top :=
    hspec.2.2
  have hdx : 0 < delta.1 := by
    have hp := hmin imax
    have hmul : 0 < (N : Int) *
        (triangularPathDisplacement (List.ofFn d)).1 := by positivity
    simp [delta, triangularPeriodStateCoord, Prod.smul_mk]
    nlinarith
  have hdisp : triangularPathDisplacement l = delta :=
    triangularPeriodicArc_displacement d N hN imin imax
  have hnodup : (triangularPathVertices l).Nodup :=
    triangularPeriodicArc_pathVertices_nodup d N hN imin imax hinj
  have hxmin := triangularPeriodicArc_xmin d N hN imin imax hmin hD
  have hxmax := triangularPeriodicArc_xmax d N hN imin imax hmax hD
  let c := triangularOutsideConnector delta.1 delta.2 top
  letI : NeZero (l ++ c).length := by
    refine ⟨?_⟩
    simp [c, triangularOutsideConnector, ons_outsideConnector]
  have hclosed : triangularPathDisplacement (l ++ c) = 0 := by
    rw [triangularPathDisplacement_append,
      triangularOutsideConnector_displacement delta.1 delta.2 top
        hdx hdy htop, hdisp]
    ext <;> simp
  have hsimple :
      (triangularPathVertices (l ++ c)).dropLast.Nodup :=
    triangularBoundingClosure_vertices_dropLast_nodup l delta.1 delta.2 top
      hdx hdy htop hdisp hnodup hxmin hxmax hymax
  have hlen : 3 ≤ (l ++ c).length := by
    have hv0 : top.toNat ≠ 0 := by
      intro h
      have := Int.toNat_eq_zero.mp h
      omega
    have hv : 1 ≤ top.toNat := Nat.one_le_iff_ne_zero.mpr hv0
    simp [c, triangularOutsideConnector, ons_outsideConnector]
    omega
  exact triangularSimpleList_phaseCycle_eq_neg_one
    (l ++ c) hclosed hsimple hlen

theorem kwVectorPhasePath_append
    (l r : List Complex) (hl : l ≠ []) (hr : r ≠ []) :
    kwVectorPhasePath (l ++ r) =
      kwVectorPhasePath l * kwVectorTurnPhase l.getLast! r.head! *
        kwVectorPhasePath r := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hr
  simpa [List.getLast!, List.head!] using
    kwVectorPhasePath_append_cons x xs y ys

theorem kwVectorPhaseCycle_eq_path_mul_turn
    (l : List Complex) (hl : l ≠ []) :
    kwVectorPhaseCycle l =
      kwVectorPhasePath l * kwVectorTurnPhase l.getLast! l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem kwVectorPhaseCycle_append
    (l r : List Complex) (hl : l ≠ []) (hr : r ≠ []) :
    kwVectorPhaseCycle (l ++ r) =
      kwVectorPhasePath l * kwVectorTurnPhase l.getLast! r.head! *
        kwVectorPhasePath r * kwVectorTurnPhase r.getLast! l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hr
  simpa [List.getLast!, List.head!] using
    kwVectorPhaseCycle_append_cons x xs y ys

theorem map_head!_of_ne_nil
    {X Y : Type*} [Inhabited X] [Inhabited Y]
    (f : X -> Y) (l : List X) (hl : l ≠ []) :
    (l.map f).head! = f l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem map_getLast!_of_ne_nil
    {X Y : Type*} [Inhabited X] [Inhabited Y]
    (f : X -> Y) (l : List X) (hl : l ≠ []) :
    (l.map f).getLast! = f l.getLast! := by
  have hmap : l.map f ≠ [] := by simpa using hl
  rw [ons_getLast!_eq_getLast (l.map f) hmap,
    ons_getLast!_eq_getLast l hl]
  exact List.getLast_map hmap

theorem kwVectorPhasePath_replicate_succ (n : Nat) (x : Complex) :
    kwVectorPhasePath (List.replicate (n + 1) x) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show List.replicate (n + 1 + 1) x =
          x :: x :: List.replicate n x by
        rw [List.replicate_succ, List.replicate_succ]]
      rw [kwVectorPhasePath_cons_cons]
      rw [show x :: List.replicate n x =
          List.replicate (n + 1) x by rw [List.replicate_succ], ih]
      simp [kwVectorTurnPhase, kwAngleTurnPhase]

theorem getLast!_replicate_succ
    {X : Type*} [Inhabited X] (n : Nat) (x : X) :
    (List.replicate (n + 1) x).getLast! = x := by
  have h : List.replicate (n + 1) x ≠ [] := by simp
  rw [ons_getLast!_eq_getLast _ h]
  exact List.getLast_replicate h

theorem kwVectorPhasePath_five_blocks
    (a b c d e : Complex) (na nb nc nd ne : Nat) :
    kwVectorPhasePath
        (List.replicate (na + 1) a ++
          List.replicate (nb + 1) b ++
          List.replicate (nc + 1) c ++
          List.replicate (nd + 1) d ++
          List.replicate (ne + 1) e) =
      kwVectorTurnPhase a b * kwVectorTurnPhase b c *
        kwVectorTurnPhase c d * kwVectorTurnPhase d e := by
  let A := List.replicate (na + 1) a
  let B := List.replicate (nb + 1) b
  let C := List.replicate (nc + 1) c
  let D := List.replicate (nd + 1) d
  let E := List.replicate (ne + 1) e
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  have hC : C ≠ [] := by simp [C]
  have hD : D ≠ [] := by simp [D]
  have hE : E ≠ [] := by simp [E]
  change kwVectorPhasePath (A ++ B ++ C ++ D ++ E) = _
  simp only [List.append_assoc]
  rw [kwVectorPhasePath_append A (B ++ (C ++ (D ++ E))) hA
      (by simp [hB]),
    kwVectorPhasePath_append B (C ++ (D ++ E)) hB (by simp [hC]),
    kwVectorPhasePath_append C (D ++ E) hC (by simp [hD]),
    kwVectorPhasePath_append D E hD hE]
  have hAlast : A.getLast! = a := by
    exact getLast!_replicate_succ na a
  have hBlast : B.getLast! = b := by
    exact getLast!_replicate_succ nb b
  have hClast : C.getLast! = c := by
    exact getLast!_replicate_succ nc c
  have hDlast : D.getLast! = d := by
    exact getLast!_replicate_succ nd d
  have hBhead : (B ++ (C ++ (D ++ E))).head! = b := by
    simp [B, List.replicate_succ]
  have hChead : (C ++ (D ++ E)).head! = c := by
    simp [C, List.replicate_succ]
  have hDhead : (D ++ E).head! = d := by
    simp [D, List.replicate_succ]
  have hEhead : E.head! = e := by
    simp [E, List.replicate_succ]
  rw [hAlast, hBlast, hClast, hDlast,
    hBhead, hChead, hDhead, hEhead]
  simp [A, B, C, D, E, kwVectorPhasePath_replicate_succ]
  ring

theorem triangularOutsideConnector_phasePath
    (dx dy top : Int) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    kwVectorPhasePath
        ((triangularOutsideConnector dx dy top).map triangularIntVector) =
      kwVectorTurnPhase (triangularIntVector 1) (triangularIntVector 3) *
        kwVectorTurnPhase (triangularIntVector 3) (triangularIntVector 0) *
        kwVectorTurnPhase (triangularIntVector 0) (triangularIntVector 2) *
        kwVectorTurnPhase (triangularIntVector 2) (triangularIntVector 1) := by
  have hu : 0 < (top - dy).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hw : 0 < (dx + 2).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hv : 0 < top.toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨u, hu'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  obtain ⟨w, hw'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  obtain ⟨v, hv'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  rw [show (triangularOutsideConnector dx dy top).map triangularIntVector =
      List.replicate (0 + 1) (triangularIntVector 1) ++
        List.replicate (u + 1) (triangularIntVector 3) ++
        List.replicate (w + 1) (triangularIntVector 0) ++
        List.replicate (v + 1) (triangularIntVector 2) ++
        List.replicate (0 + 1) (triangularIntVector 1) by
      simp [triangularOutsideConnector, ons_outsideConnector,
        triangularAxisDirection, hu', hw', hv', List.map_replicate]]
  exact kwVectorPhasePath_five_blocks _ _ _ _ _ 0 u w v 0

@[simp] theorem triangularOutsideConnector_head
    (dx dy top : Int) :
    (triangularOutsideConnector dx dy top).head! = 1 := by
  simp [triangularOutsideConnector, ons_outsideConnector,
    triangularAxisDirection]

@[simp] theorem triangularOutsideConnector_getLast
    (dx dy top : Int) :
    (triangularOutsideConnector dx dy top).getLast! = 1 := by
  simp [triangularOutsideConnector, ons_outsideConnector,
    triangularAxisDirection, List.getLast!]

theorem triangularOfFn_ne_nil {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) : List.ofFn d ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  exact NeZero.ne n this

theorem triangularDrop_ofFn_ne_nil {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (i : Fin n) :
    (List.ofFn d).drop i.val ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [List.length_drop, List.length_ofFn] at this
  simp at this
  omega

end StatMech.FrontierA
