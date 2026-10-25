/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part7


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_pathVertices_map_dropLast_of_chain
    {X : Type*} [Inhabited X]
    (coord : X → ℤ × ℤ) (dir : X → Fin 4)
    (s : List X) (hs : s ≠ [])
    (hchain : List.IsChain
      (fun a b ↦ coord b = coord a + stepOf (dir a)) s) :
    ons_pathVertices (s.dropLast.map dir) =
      s.map (fun x ↦ coord x - coord s.head!) := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons a as ih =>
      cases as with
      | nil => simp [ons_pathVertices, List.head!]
      | cons b bs =>
          have hc := List.isChain_cons_cons.mp hchain
          have ih' := ih (by simp) hc.2
          rw [List.dropLast_cons_of_ne_nil (by simp), List.map_cons,
            ons_pathVertices_cons, ih']
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

theorem ons_periodicArc_pathVertices {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_pathVertices (ons_periodicArcDirections d N imin imax) =
      (ons_periodicArcStates N imin imax).map
        (fun z ↦ ons_periodStateCoord d z -
          ons_periodStateCoord d (0, imin)) := by
  rw [ons_periodicArcDirections]
  have hs : ons_periodicArcStates N imin imax ≠ [] := by
    intro h
    have hh := ons_periodicArcStates_head? N hN imin imax
    rw [h] at hh
    simp at hh
  have h := ons_pathVertices_map_dropLast_of_chain
    (ons_periodStateCoord d) (fun z ↦ d z.2)
    (ons_periodicArcStates N imin imax) hs
    (ons_periodicArcStates_isChain d N imin imax)
  rw [show (ons_periodicArcStates N imin imax).head! = (0, imin) by
    have hh := ons_periodicArcStates_head? N hN imin imax
    cases hs' : ons_periodicArcStates N imin imax with
    | nil => simp [hs'] at hh
    | cons a as => simpa [hs'] using hh] at h
  exact h

theorem ons_periodicArc_pathVertices_nodup {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (ons_periodStateCoord d)) :
    (ons_pathVertices
      (ons_periodicArcDirections d N imin imax)).Nodup := by
  rw [ons_periodicArc_pathVertices d N hN imin imax]
  apply List.Nodup.map (by
    intro a b hab
    apply hinj
    apply sub_left_injective
    exact hab)
  exact ons_periodicArcStates_nodup N imin imax

theorem ons_periodicArc_displacement {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_pathDisplacement (ons_periodicArcDirections d N imin imax) =
      ons_periodStateCoord d (N, imax) -
        ons_periodStateCoord d (0, imin) := by
  have hlast := ons_pathVertices_getLast
    (ons_periodicArcDirections d N imin imax)
  rw [ons_periodicArc_pathVertices d N hN imin imax,
    List.getLast?_map, ons_periodicArcStates_getLast? N hN] at hlast
  exact Option.some.inj hlast.symm

theorem ons_periodicArc_xmin {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmin : ∀ i, (pos d imin).1 ≤ (pos d i).1)
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (ons_pathVertices
      (ons_periodicArcDirections d N imin imax)).dropLast,
      0 ≤ z.1 := by
  intro z hz
  have hz' : z ∈ ons_pathVertices
      (ons_periodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [ons_periodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmin s.2
  simp [ons_periodStateCoord, Prod.smul_mk]
  nlinarith [Nat.zero_le s.1]

theorem ons_periodicArc_xmax {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmax : ∀ i, (pos d i).1 ≤ (pos d imax).1)
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (ons_pathVertices
      (ons_periodicArcDirections d N imin imax)).dropLast,
      z.1 ≤
        (ons_periodStateCoord d (N, imax) -
          ons_periodStateCoord d (0, imin)).1 := by
  intro z hz
  have hz' : z ∈ ons_pathVertices
      (ons_periodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [ons_periodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmax s.2
  have hr := ons_mem_periodicArcStates_fst_le N imin imax s hs
  simp [ons_periodStateCoord, Prod.smul_mk]
  nlinarith

theorem ons_exists_path_top (l : List (Fin 4)) (dy : ℤ) :
    ∃ top : ℤ, 0 < top ∧ dy < top ∧
      ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top := by
  let ys := ((ons_pathVertices l).dropLast.map
    (fun z ↦ z.2.natAbs)).sum
  let top : ℤ := (dy.natAbs + ys + 1 : ℕ)
  refine ⟨top, ?_, ?_, ?_⟩
  · simp [top]
    positivity
  · have hdy : dy ≤ (dy.natAbs : ℤ) := Int.le_natAbs
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hys : (0 : ℤ) ≤ ys := by positivity
    omega
  · intro z hz
    have hmem : z.2.natAbs ∈
        (ons_pathVertices l).dropLast.map (fun w ↦ w.2.natAbs) :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    have hleNat : z.2.natAbs ≤ ys :=
      List.le_sum_of_mem hmem
    have hle : z.2 ≤ (z.2.natAbs : ℤ) := Int.le_natAbs
    have hcast : (z.2.natAbs : ℤ) ≤ ys := by exact_mod_cast hleNat
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hdy0 : (0 : ℤ) ≤ dy.natAbs := by positivity
    omega

theorem ons_periodicArc_adjustedTurn_eq_four_or_neg_four
    {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (ons_periodStateCoord d))
    (hmin : ∀ i, (pos d imin).1 ≤ (pos d i).1)
    (hmax : ∀ i, (pos d i).1 ≤ (pos d imax).1)
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    let l := ons_periodicArcDirections d N imin imax
    ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
        ons_turnPow 0 l.head! = 4 ∨
      ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
        ons_turnPow 0 l.head! = -4 := by
  let l := ons_periodicArcDirections d N imin imax
  let delta := ons_periodStateCoord d (N, imax) -
    ons_periodStateCoord d (0, imin)
  have hdx : 0 < delta.1 := by
    have hp := hmin imax
    have hmul : 0 < (N : ℤ) *
        (ons_pathDisplacement (List.ofFn d)).1 := by
      positivity
    simp [delta, ons_periodStateCoord, Prod.smul_mk]
    nlinarith
  have hdisp : ons_pathDisplacement l = delta := by
    exact ons_periodicArc_displacement d N hN imin imax
  have hnodup : (ons_pathVertices l).Nodup :=
    ons_periodicArc_pathVertices_nodup d N hN imin imax hinj
  have hxmin := ons_periodicArc_xmin d N hN imin imax hmin hD
  have hxmax := ons_periodicArc_xmax d N hN imin imax hmax hD
  obtain ⟨top, htop, hdy, hymax⟩ := ons_exists_path_top l delta.2
  have hturn := ons_boundingClosure_turnSum_eq_four_or_neg_four
    l delta.1 delta.2 top hdx hdy htop hdisp hnodup hxmin hxmax hymax
  have hln : l ≠ [] := by
    intro hl
    have hslen := ons_periodicArcStates_length N hN imin imax
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
    have hdirlen := congrArg List.length hl
    simp [l, ons_periodicArcDirections] at hdirlen
    omega
  rw [ons_boundingClosure_cyclicTurnSum l hln
    delta.1 delta.2 top hdx hdy htop] at hturn
  exact hturn

end StatMech.Onsager
