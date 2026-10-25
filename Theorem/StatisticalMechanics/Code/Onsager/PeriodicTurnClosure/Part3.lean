/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part3


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_outsideConnector_vertices_dropLast_eq
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast =
      ons_outsideConnectorVertexList dx dy top := by
  let B := List.replicate (top - dy).toNat (1 : Fin 4)
  let C := List.replicate (dx + 2).toNat (2 : Fin 4)
  let D := List.replicate top.toNat (3 : Fin 4)
  have hu : 0 ≤ top - dy := by omega
  have hw : 0 ≤ dx + 2 := by omega
  have hv : 0 ≤ top := by omega
  have hshape : ons_outsideConnector dx dy top =
      [0] ++ (B ++ (C ++ (D ++ [0]))) := by
    simp [ons_outsideConnector, B, C, D, List.append_assoc]
  rw [hshape,
    ons_pathVertices_append_dropLast [0] (B ++ (C ++ (D ++ [0]))),
    ons_pathVertices_append_dropLast B (C ++ (D ++ [0])),
    ons_pathVertices_append_dropLast C (D ++ [0]),
    ons_pathVertices_append_dropLast D [0],
    ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [B, C, D, ons_outsideConnectorVertexList,
    ons_pathDisplacement_replicate, ons_pathDisplacement,
    stepOf, Prod.smul_mk, Int.toNat_of_nonneg hu,
    Int.toNat_of_nonneg hw, Int.toNat_of_nonneg hv]
  repeat' first
    | apply congrArg₂ List.append <;> try rfl
    | apply List.map_congr_left
      intro k hk
      apply Prod.ext <;> simp <;> ring
  all_goals
    first
    | rw [← List.map_eq_flatMap, List.map_map]
      apply List.map_congr_left
      intro k hk
      apply Prod.ext <;>
        simp [Function.comp_def, stepOf, Prod.smul_mk] <;> ring
    | rw [ons_map_pathVertices_replicate_dropLast,
          ← List.map_eq_flatMap, List.map_map]
      apply List.map_congr_left
      intro k hk
      apply Prod.ext <;>
        simp [Function.comp_def, stepOf, Prod.smul_mk] <;> ring
    | congr 2 <;> ring

theorem ons_outsideConnectorVertexList_nodup
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (ons_outsideConnectorVertexList dx dy top).Nodup := by
  simp [ons_outsideConnectorVertexList, List.nodup_append]
  repeat' apply And.intro
  all_goals
    first
    | omega
    | intro h
      have hx := congrArg (fun z : ℤ × ℤ ↦ z.1) h
      simp at hx
      omega
    | rw [← List.map_eq_flatMap, List.map_map]
      apply List.Nodup.map (by
        intro a b hab
        simp only [Function.comp_apply, Prod.mk.injEq] at hab
        omega)
      exact List.nodup_range

theorem ons_outsideConnector_vertices_dropLast_nodup
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (ons_pathVertices (ons_outsideConnector dx dy top)).dropLast.Nodup := by
  rw [ons_outsideConnector_vertices_dropLast_eq dx dy top hdx hdy htop]
  exact ons_outsideConnectorVertexList_nodup dx dy top hdx hdy htop

theorem ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup
    (l : List (Fin 4)) (hnodup : (ons_pathVertices l).Nodup) :
    ons_pathDisplacement l ∉ (ons_pathVertices l).dropLast := by
  have hne : ons_pathVertices l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hlast : (ons_pathVertices l).getLast hne =
      ons_pathDisplacement l := by
    have h := ons_pathVertices_getLast l
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  rw [← List.dropLast_append_getLast hne] at hnodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  intro hmem
  exact hdisj (ons_pathDisplacement l) hmem
    ((ons_pathVertices l).getLast hne) (by simp) hlast.symm

theorem ons_outsideConnector_shift_disjoint
    (l : List (Fin 4)) (dx dy top : ℤ)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hnodup : (ons_pathVertices l).Nodup)
    (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
    ∀ z ∈ (ons_pathVertices l).dropLast,
      ∀ w ∈ (ons_pathVertices
        (ons_outsideConnector dx dy top)).dropLast,
        z ≠ ons_pathDisplacement l + w := by
  intro z hz w hw heq
  have hend : (dx, dy) ∉ (ons_pathVertices l).dropLast := by
    simpa [hdisp] using
      ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup l hnodup
  rcases ons_mem_outsideConnector_vertices_dropLast
      dx dy top hdx hdy htop w hw with
    rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      ⟨k, hk, rfl⟩ | rfl
  · have hzeq : z = (dx, dy) := by simpa [hdisp] using heq
    exact hend (hzeq ▸ hz)
  · have hx := congrArg Prod.fst heq
    have := hxmax z hz
    simp [hdisp] at hx
    omega
  · have hy := congrArg Prod.snd heq
    have := hymax z hz
    have hk' : (k : ℤ) < dx + 2 := by
      simpa [Int.toNat_of_nonneg (show 0 ≤ dx + 2 by omega)] using hk
    simp [hdisp] at hy
    omega
  · have hx := congrArg Prod.fst heq
    have := hxmin z hz
    simp [hdisp] at hx
    omega
  · have hx := congrArg Prod.fst heq
    have := hxmin z hz
    simp [hdisp] at hx
    omega

theorem ons_boundingClosure_vertices_dropLast_nodup
    (l : List (Fin 4)) (dx dy top : ℤ)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hnodup : (ons_pathVertices l).Nodup)
    (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
    (ons_pathVertices
      (l ++ ons_outsideConnector dx dy top)).dropLast.Nodup := by
  rw [ons_pathVertices_append_dropLast]
  have hleft : (ons_pathVertices l).dropLast.Nodup :=
    List.Nodup.sublist (List.dropLast_sublist _) hnodup
  have hright :
      ((ons_pathVertices
        (ons_outsideConnector dx dy top)).dropLast.map
          (ons_pathDisplacement l + ·)).Nodup :=
    (ons_outsideConnector_vertices_dropLast_nodup
      dx dy top hdx hdy htop).map (add_right_injective _)
  apply List.Nodup.append hleft hright
  rw [List.disjoint_iff_ne]
  intro z hz b hb
  rw [List.mem_map] at hb
  obtain ⟨w, hw, rfl⟩ := hb
  exact ons_outsideConnector_shift_disjoint l dx dy top hdx hdy htop
    hdisp hnodup hxmin hxmax hymax z hz w hw

theorem ons_pos_succ_eq_head_add_pos_tail
    {n : ℕ} [NeZero n] (d : Fin (n + 1) → Fin 4) (i : Fin n) :
    pos d i.succ =
      stepOf (d 0) + pos (fun j : Fin n ↦ d j.succ) i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction i using Fin.induction with
  | zero =>
      rw [ons_pos_succ_cast d 0]
      simp [pos]
  | succ i ih =>
      rw [ons_pos_succ_cast d i.succ]
      have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hi, ih, ons_pos_succ_cast (fun j ↦ d j.succ) i]
      abel

theorem ons_pathVertices_dropLast_eq_ofFn_pos
    (l : List (Fin 4)) [NeZero l.length] :
    (ons_pathVertices l).dropLast =
      List.ofFn (pos (fun i : Fin l.length ↦ l.get i)) := by
  have hl : l ≠ [] := by
    intro h
    subst l
    exact NeZero.ne 0 rfl
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases ds with
  | nil =>
      simp [ons_pathVertices, List.ofFn_succ, pos]
  | cons e es =>
      letI : NeZero (e :: es).length := ⟨by simp⟩
      have ih := ons_pathVertices_dropLast_eq_ofFn_pos (e :: es)
      have hmap :
          (ons_pathVertices (e :: es)).map (stepOf d + ·) ≠ [] := by
        simp
      rw [ons_pathVertices_cons,
        List.dropLast_cons_of_ne_nil hmap, ← List.map_dropLast, ih]
      conv_rhs => rw [List.ofFn_succ]
      change 0 :: _ = pos (fun i : Fin (d :: e :: es).length ↦
        (d :: e :: es).get i) 0 :: _
      rw [show pos (fun i : Fin (d :: e :: es).length ↦
        (d :: e :: es).get i) 0 = 0 by simp [pos]]
      congr 1
      rw [List.map_ofFn]
      congr 1
      funext i
      exact (ons_pos_succ_eq_head_add_pos_tail
        (fun j : Fin ((e :: es).length + 1) ↦
          (d :: e :: es).get j) i).symm

theorem ons_pos_get_injective_of_vertices_dropLast_nodup
    (l : List (Fin 4)) [NeZero l.length]
    (hnodup : (ons_pathVertices l).dropLast.Nodup) :
    Function.Injective (pos (fun i : Fin l.length ↦ l.get i)) := by
  rw [ons_pathVertices_dropLast_eq_ofFn_pos] at hnodup
  exact List.nodup_ofFn.mp hnodup

theorem ons_pathDisplacement_eq_sum_map (l : List (Fin 4)) :
    ons_pathDisplacement l = (l.map stepOf).sum := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

theorem ons_pathDisplacement_ofFn {n : ℕ} (d : Fin n → Fin 4) :
    ons_pathDisplacement (List.ofFn d) = ∑ i, stepOf (d i) := by
  rw [ons_pathDisplacement_eq_sum_map, List.map_ofFn,
    List.sum_ofFn]
  simp [Function.comp_def]

theorem ons_openTurnSum_ofFn {n : ℕ} (d : Fin (n + 1) → Fin 4) :
    ons_openTurnSum (List.ofFn d) =
      ∑ i : Fin n, ons_turnPow (d i.castSucc) (d i.succ) := by
  induction n with
  | zero => simp [List.ofFn_succ]
  | succ n ih =>
      rw [List.ofFn_succ]
      set g : Fin (n + 1) → Fin 4 := fun i ↦ d i.succ with hg
      have hgcons : List.ofFn g =
          g 0 :: List.ofFn (fun i : Fin n ↦ g i.succ) := by
        rw [List.ofFn_succ]
      rw [hgcons, ons_openTurnSum_cons_cons, ← hgcons, ih g,
        Fin.sum_univ_succ]
      simp only [hg, Fin.castSucc_zero, Fin.succ_castSucc]

theorem ons_getLast!_ofFn {X : Type*} [Inhabited X]
    {n : ℕ} (f : Fin (n + 1) → X) :
    (List.ofFn f).getLast! = f (Fin.last n) := by
  cases n with
  | zero => simp [List.ofFn_succ, List.getLast!]
  | succ n =>
      rw [List.ofFn_succ]
      dsimp only [List.getLast!]
      rw [List.getLast_cons (by simp)]
      rw [List.getLast_ofFn (by simp)]
      congr 1

theorem ons_cyclicTurnSum_ofFn {n : ℕ} (d : Fin (n + 1) → Fin 4) :
    ons_cyclicTurnSum (List.ofFn d) =
      ∑ i, ons_turnPow (d i) (d (i + 1)) := by
  rw [show ons_cyclicTurnSum (List.ofFn d) =
      ons_openTurnSum (List.ofFn d) +
        ons_turnPow (List.ofFn d).getLast! (d 0) by
    simp only [List.ofFn_succ]
    rfl]
  rw [ons_openTurnSum_ofFn, Fin.sum_univ_castSucc,
    ons_getLast!_ofFn]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Fin.ext
    simp
  · rw [Fin.last_add_one]

theorem ons_cyclicTurnSum_ofFn' {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) :
    ons_cyclicTurnSum (List.ofFn d) =
      ∑ i, ons_turnPow (d i) (d (i + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact ons_cyclicTurnSum_ofFn d

theorem ons_cyclicTurnSum_eq_four_or_neg_four_of_list
    (l : List (Fin 4)) [NeZero l.length]
    (hclosed : ons_pathDisplacement l = 0)
    (hsimple : (ons_pathVertices l).dropLast.Nodup)
    (hlen : 3 ≤ l.length)
    (hnu : ∀ i : Fin l.length, l.get (i + 1) ≠ l.get i + 2) :
    ons_cyclicTurnSum l = 4 ∨ ons_cyclicTurnSum l = -4 := by
  let d : Fin l.length → Fin 4 := fun i ↦ l.get i
  have hsum : ∑ i, stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup l hsimple
  have hturn :=
    GeneralUmlaufsatz.turnSum_eq_four_or_neg_four
      d hsum hinj hlen hnu
  rw [← ons_cyclicTurnSum_ofFn', List.ofFn_get] at hturn
  exact hturn

theorem ons_stepOf_add_two (w : Fin 4) :
    stepOf (w + 2) = -stepOf w := by
  fin_cases w <;> rfl

theorem ons_nonUturn_of_pos_injective
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0)
    (hinj : Function.Injective (pos d)) (hn : 3 ≤ n) :
    ∀ i, d (i + 1) ≠ d i + 2 := by
  intro i hdir
  have heq : pos d (i + 1 + 1) = pos d i := by
    rw [NoDoubleWind.pos_succ d hclosed (i + 1),
      NoDoubleWind.pos_succ d hclosed i, hdir, ons_stepOf_add_two]
    exact add_neg_cancel_right _ _
  have hidx := hinj heq
  have htwo : (2 : Fin n) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change 2 % n = 0 at hv
    rw [Nat.mod_eq_of_lt hn] at hv
    omega
  apply htwo
  calc
    (2 : Fin n) = 1 + 1 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt hn]
    _ = -i + (i + 1 + 1) := by abel
    _ = -i + i := by rw [hidx]
    _ = 0 := neg_add_cancel i

theorem ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list
    (l : List (Fin 4)) [NeZero l.length]
    (hclosed : ons_pathDisplacement l = 0)
    (hsimple : (ons_pathVertices l).dropLast.Nodup)
    (hlen : 3 ≤ l.length) :
    ons_cyclicTurnSum l = 4 ∨ ons_cyclicTurnSum l = -4 := by
  let d : Fin l.length → Fin 4 := fun i ↦ l.get i
  have hsum : ∑ i, stepOf (d i) = 0 := by
    rw [← ons_pathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (pos d) :=
    ons_pos_get_injective_of_vertices_dropLast_nodup l hsimple
  exact ons_cyclicTurnSum_eq_four_or_neg_four_of_list l hclosed
    hsimple hlen (ons_nonUturn_of_pos_injective d hsum hinj hlen)

theorem ons_boundingClosure_turnSum_eq_four_or_neg_four
    (l : List (Fin 4)) (dx dy top : ℤ)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : ons_pathDisplacement l = (dx, dy))
    (hnodup : (ons_pathVertices l).Nodup)
    (hxmin : ∀ z ∈ (ons_pathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (ons_pathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (ons_pathVertices l).dropLast, z.2 < top) :
    ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = 4 ∨
      ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) = -4 := by
  let c := ons_outsideConnector dx dy top
  letI : NeZero (l ++ c).length := ⟨by simp [c, ons_outsideConnector]⟩
  have hclosed : ons_pathDisplacement (l ++ c) = 0 := by
    rw [ons_pathDisplacement_append,
      ons_outsideConnector_displacement dx dy top hdx hdy htop,
      hdisp]
    ext <;> simp
  have hsimple : (ons_pathVertices (l ++ c)).dropLast.Nodup := by
    exact ons_boundingClosure_vertices_dropLast_nodup l dx dy top
      hdx hdy htop hdisp hnodup hxmin hxmax hymax
  have hlen : 3 ≤ (l ++ c).length := by
    have hv0 : top.toNat ≠ 0 := by
      intro h
      have := Int.toNat_eq_zero.mp h
      omega
    have hv : 1 ≤ top.toNat := Nat.one_le_iff_ne_zero.mpr hv0
    simp [c, ons_outsideConnector]
    omega
  exact ons_cyclicTurnSum_eq_four_or_neg_four_of_simple_list
    (l ++ c) hclosed hsimple hlen

theorem ons_getLast!_eq_getLast {X : Type*} [Inhabited X]
    (l : List X) (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a as => rfl

theorem ons_boundingClosure_cyclicTurnSum
    (l : List (Fin 4)) (hl : l ≠ [])
    (dx dy top : ℤ) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    ons_cyclicTurnSum (l ++ ons_outsideConnector dx dy top) =
      ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
        ons_turnPow 0 l.head! := by
  let c := ons_outsideConnector dx dy top
  have hc : c ≠ [] := ons_outsideConnector_ne_nil dx dy top
  rw [show ons_cyclicTurnSum (l ++ c) =
      ons_openTurnSum (l ++ c) +
        ons_turnPow (l ++ c).getLast! (l ++ c).head! by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hl
    rfl]
  rw [ons_openTurnSum_append l c hl hc,
    ons_outsideConnector_openTurnSum dx dy top hdx hdy htop]
  have hlast : (l ++ c).getLast! = 0 := by
    have happ : l ++ c ≠ [] := List.append_ne_nil_of_right_ne_nil l hc
    have heq : (l ++ c).getLast happ = c.getLast hc := by
      rw [List.getLast_append]
      simp [hc]
    rw [ons_getLast!_eq_getLast (l ++ c) happ]
    rw [heq]
    rw [← ons_getLast!_eq_getLast c hc]
    exact ons_outsideConnector_getLast dx dy top
  have hhead : (l ++ c).head! = l.head! := by simp [hl]
  have hchead : c.head! = 0 := by
    simpa only [c] using ons_outsideConnector_head dx dy top
  rw [hlast, hhead, hchead]

theorem ons_three_values_force_step_zero
    (a t : ℤ)
    (h0 : a = 4 ∨ a = -4)
    (h1 : a + t = 4 ∨ a + t = -4)
    (h2 : a + 2 * t = 4 ∨ a + 2 * t = -4) :
    t = 0 := by
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;> omega

end StatMech.Onsager
