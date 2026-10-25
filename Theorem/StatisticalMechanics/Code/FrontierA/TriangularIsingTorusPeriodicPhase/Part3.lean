/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

theorem triangularOutsideConnector_displacement
    (dx dy top : Int) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    triangularPathDisplacement (triangularOutsideConnector dx dy top) =
      (-dx, -dy) := by
  rw [triangularOutsideConnector, triangularPathDisplacement_map_axis]
  exact ons_outsideConnector_displacement dx dy top hdx hdy htop

theorem triangularOutsideConnector_vertices_dropLast_nodup
    (dx dy top : Int) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (triangularPathVertices
      (triangularOutsideConnector dx dy top)).dropLast.Nodup := by
  rw [triangularOutsideConnector, triangularPathVertices_map_axis]
  exact ons_outsideConnector_vertices_dropLast_nodup
    dx dy top hdx hdy htop

theorem triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup
    (l : List (Fin 6)) (hnodup : (triangularPathVertices l).Nodup) :
    triangularPathDisplacement l ∉ (triangularPathVertices l).dropLast := by
  have hne : triangularPathVertices l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hlast : (triangularPathVertices l).getLast hne =
      triangularPathDisplacement l := by
    have h := triangularPathVertices_getLast l
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  rw [<- List.dropLast_append_getLast hne] at hnodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  intro hmem
  exact hdisj (triangularPathDisplacement l) hmem
    ((triangularPathVertices l).getLast hne) (by simp) hlast.symm

theorem triangularOutsideConnector_shift_disjoint
    (l : List (Fin 6)) (dx dy top : Int)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : triangularPathDisplacement l = (dx, dy))
    (hnodup : (triangularPathVertices l).Nodup)
    (hxmin : ∀ z ∈ (triangularPathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (triangularPathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top) :
    ∀ z ∈ (triangularPathVertices l).dropLast,
      ∀ w ∈ (triangularPathVertices
        (triangularOutsideConnector dx dy top)).dropLast,
        z ≠ triangularPathDisplacement l + w := by
  intro z hz w hw heq
  have hend : (dx, dy) ∉ (triangularPathVertices l).dropLast := by
    simpa [hdisp] using
      triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup l hnodup
  rw [triangularOutsideConnector, triangularPathVertices_map_axis] at hw
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
    have hk' : (k : Int) < dx + 2 := by
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

theorem triangularBoundingClosure_vertices_dropLast_nodup
    (l : List (Fin 6)) (dx dy top : Int)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : triangularPathDisplacement l = (dx, dy))
    (hnodup : (triangularPathVertices l).Nodup)
    (hxmin : ∀ z ∈ (triangularPathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (triangularPathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top) :
    (triangularPathVertices
      (l ++ triangularOutsideConnector dx dy top)).dropLast.Nodup := by
  rw [triangularPathVertices_append_dropLast]
  have hleft : (triangularPathVertices l).dropLast.Nodup :=
    List.Nodup.sublist (List.dropLast_sublist _) hnodup
  have hright :
      ((triangularPathVertices
        (triangularOutsideConnector dx dy top)).dropLast.map
          (triangularPathDisplacement l + ·)).Nodup :=
    (triangularOutsideConnector_vertices_dropLast_nodup
      dx dy top hdx hdy htop).map (add_right_injective _)
  apply List.Nodup.append hleft hright
  rw [List.disjoint_iff_ne]
  intro z hz b hb
  rw [List.mem_map] at hb
  obtain ⟨w, hw, rfl⟩ := hb
  exact triangularOutsideConnector_shift_disjoint l dx dy top
    hdx hdy htop hdisp hnodup hxmin hxmax hymax z hz w hw

theorem triangularPeriodicIntPos_succ_cast
    {m : Nat} (direction : Fin (m + 1) -> Fin 6) (i : Fin m) :
    triangularIntPos direction i.succ =
      triangularIntPos direction i.castSucc +
        triangularIntStep (direction i.castSucc) := by
  have hfilter :
      (Finset.univ.filter (fun j : Fin (m + 1) => j < i.succ)) =
        insert i.castSucc
          (Finset.univ.filter
            (fun j : Fin (m + 1) => j < i.castSucc)) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hj
      rw [Fin.lt_def] at hj
      simp only [Fin.val_succ] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Or.inr (Fin.lt_def.mpr hlt)
      · exact Or.inl (Fin.ext heq)
    · rintro (rfl | hj)
      · exact Fin.castSucc_lt_succ
      · exact hj.trans Fin.castSucc_lt_succ
  have hnotmem : i.castSucc ∉
      (Finset.univ.filter
        (fun j : Fin (m + 1) => j < i.castSucc)) := by simp
  rw [triangularIntPos, triangularIntPos, hfilter,
    Finset.sum_insert hnotmem, add_comm]

theorem triangularPos_succ_eq_head_add_pos_tail
    {n : Nat} [NeZero n] (d : Fin (n + 1) -> Fin 6) (i : Fin n) :
    triangularIntPos d i.succ =
      triangularIntStep (d 0) +
        triangularIntPos (fun j : Fin n => d j.succ) i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction i using Fin.induction with
  | zero =>
      rw [triangularPeriodicIntPos_succ_cast d 0]
      simp [triangularIntPos]
  | succ i ih =>
      rw [triangularPeriodicIntPos_succ_cast d i.succ]
      have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hi, ih,
        triangularPeriodicIntPos_succ_cast (fun j => d j.succ) i]
      abel

theorem triangularPathVertices_dropLast_eq_ofFn_pos
    (l : List (Fin 6)) [NeZero l.length] :
    (triangularPathVertices l).dropLast =
      List.ofFn (triangularIntPos (fun i : Fin l.length => l.get i)) := by
  have hl : l ≠ [] := by
    intro h
    subst l
    exact NeZero.ne 0 rfl
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases ds with
  | nil => simp [triangularPathVertices, List.ofFn_succ, triangularIntPos]
  | cons e es =>
      letI : NeZero (e :: es).length := ⟨by simp⟩
      have ih := triangularPathVertices_dropLast_eq_ofFn_pos (e :: es)
      have hmap :
          (triangularPathVertices (e :: es)).map
            (triangularIntStep d + ·) ≠ [] := by simp
      rw [triangularPathVertices_cons,
        List.dropLast_cons_of_ne_nil hmap, <- List.map_dropLast, ih]
      conv_rhs => rw [List.ofFn_succ]
      change 0 :: _ = triangularIntPos
        (fun i : Fin (d :: e :: es).length => (d :: e :: es).get i) 0 :: _
      rw [show triangularIntPos
        (fun i : Fin (d :: e :: es).length => (d :: e :: es).get i) 0 = 0 by
          simp [triangularIntPos]]
      congr 1
      rw [List.map_ofFn]
      congr 1
      funext i
      exact (triangularPos_succ_eq_head_add_pos_tail
        (fun j : Fin ((e :: es).length + 1) => (d :: e :: es).get j) i).symm

theorem triangularPos_get_injective_of_vertices_dropLast_nodup
    (l : List (Fin 6)) [NeZero l.length]
    (hnodup : (triangularPathVertices l).dropLast.Nodup) :
    Function.Injective
      (triangularIntPos (fun i : Fin l.length => l.get i)) := by
  rw [triangularPathVertices_dropLast_eq_ofFn_pos] at hnodup
  exact List.nodup_ofFn.mp hnodup

theorem triangularPathDisplacement_eq_sum_map (l : List (Fin 6)) :
    triangularPathDisplacement l = (l.map triangularIntStep).sum := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

theorem triangularPathDisplacement_ofFn
    {n : Nat} (d : Fin n -> Fin 6) :
    triangularPathDisplacement (List.ofFn d) =
      ∑ i, triangularIntStep (d i) := by
  rw [triangularPathDisplacement_eq_sum_map, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def]

theorem triangularSimpleList_phaseCycle_eq_neg_one
    (l : List (Fin 6)) [NeZero l.length]
    (hclosed : triangularPathDisplacement l = 0)
    (hsimple : (triangularPathVertices l).dropLast.Nodup)
    (hlen : 3 ≤ l.length) :
    kwVectorPhaseCycle (l.map triangularIntVector) = -1 := by
  let d : Fin l.length -> Fin 6 := fun i => l.get i
  have hsum : ∑ i, triangularIntStep (d i) = 0 := by
    rw [<- triangularPathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (triangularIntPos d) :=
    triangularPos_get_injective_of_vertices_dropLast_nodup l hsimple
  let polygon := triangularIntSimplePolygon d hsum hlen hinj
  have hpolygon := kwFiniteSimplePolygonPhaseSign_adaptive polygon
  have hedges : polygon.edgeList =
      List.ofFn (fun i => triangularIntVector (d i)) := by
    unfold KWFiniteSimplePolygon.edgeList
    congr 1
    funext i
    dsimp only [polygon]
    exact triangularIntSimplePolygon_edgeVector d hsum hlen hinj i
  rw [hedges] at hpolygon
  simpa [d, <- List.map_ofFn] using hpolygon

end StatMech.FrontierA
