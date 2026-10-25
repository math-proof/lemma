/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

@[simp] theorem ons_pathDisplacement_nil :
    ons_pathDisplacement [] = 0 := rfl

@[simp] theorem ons_pathDisplacement_cons (d : Fin 4) (ds : List (Fin 4)) :
    ons_pathDisplacement (d :: ds) =
      stepOf d + ons_pathDisplacement ds := rfl

@[simp] theorem ons_pathVertices_nil :
    ons_pathVertices [] = [0] := rfl

@[simp] theorem ons_pathVertices_cons (d : Fin 4) (ds : List (Fin 4)) :
    ons_pathVertices (d :: ds) =
      0 :: (ons_pathVertices ds).map (stepOf d + ·) := rfl

theorem ons_pathDisplacement_append (l r : List (Fin 4)) :
    ons_pathDisplacement (l ++ r) =
      ons_pathDisplacement l + ons_pathDisplacement r := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      simp only [List.cons_append, ons_pathDisplacement_cons, ih]
      abel

@[simp] theorem ons_pathVertices_length (l : List (Fin 4)) :
    (ons_pathVertices l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

@[simp] theorem ons_pathVertices_head (l : List (Fin 4)) :
    (ons_pathVertices l).head? = some 0 := by
  cases l <;> rfl

theorem ons_pathVertices_getLast (l : List (Fin 4)) :
    (ons_pathVertices l).getLast? = some (ons_pathDisplacement l) := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [ons_pathVertices_cons, List.getLast?_cons,
        List.getLast?_map, ih,
        Option.map_some, ons_pathDisplacement_cons]
      simp

theorem ons_pathVertices_append (l r : List (Fin 4)) :
    ons_pathVertices (l ++ r) =
      (ons_pathVertices l).dropLast ++
        (ons_pathVertices r).map (ons_pathDisplacement l + ·) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      have hmap :
          (ons_pathVertices ds).map (stepOf d + ·) ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_map, ons_pathVertices_length] at hlen
        simp at hlen
      simp only [List.cons_append, ons_pathVertices_cons, ih,
        List.map_append, List.map_map,
        List.dropLast_cons_of_ne_nil hmap,
        ← List.map_dropLast, ons_pathDisplacement_cons]
      congr 2
      apply List.map_congr_left
      intro z hz
      simp only [Function.comp_apply]
      abel

theorem ons_pathVertices_append_dropLast
    (l r : List (Fin 4)) :
    (ons_pathVertices (l ++ r)).dropLast =
      (ons_pathVertices l).dropLast ++
        (ons_pathVertices r).dropLast.map
          (ons_pathDisplacement l + ·) := by
  rw [ons_pathVertices_append]
  have hne :
      (ons_pathVertices r).map (ons_pathDisplacement l + ·) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [List.length_map, ons_pathVertices_length] at hlen
    simp at hlen
  rw [List.dropLast_append_of_ne_nil hne, ← List.map_dropLast]

theorem ons_mem_pathVertices_append_dropLast_iff
    (l r : List (Fin 4)) (z : ℤ × ℤ) :
    z ∈ (ons_pathVertices (l ++ r)).dropLast ↔
      z ∈ (ons_pathVertices l).dropLast ∨
        ∃ w ∈ (ons_pathVertices r).dropLast,
          z = ons_pathDisplacement l + w := by
  rw [ons_pathVertices_append_dropLast, List.mem_append, List.mem_map]
  constructor
  · rintro (hz | ⟨w, hw, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (hz | ⟨w, hw, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨w, hw, rfl⟩

@[simp] theorem ons_openTurnSum_nil : ons_openTurnSum [] = 0 := rfl

@[simp] theorem ons_openTurnSum_singleton (d : Fin 4) :
    ons_openTurnSum [d] = 0 := rfl

theorem ons_openTurnSum_cons_cons
    (d e : Fin 4) (ds : List (Fin 4)) :
    ons_openTurnSum (d :: e :: ds) =
      ons_turnPow d e + ons_openTurnSum (e :: ds) := rfl

theorem ons_openTurnSum_append
    (l r : List (Fin 4)) (hl : l ≠ []) (hr : r ≠ []) :
    ons_openTurnSum (l ++ r) =
      ons_openTurnSum l +
        ons_turnPow l.getLast! r.head! + ons_openTurnSum r := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons d ds ih =>
      cases ds with
      | nil =>
          obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil hr
          simp [ons_openTurnSum]
      | cons e es =>
          have htail : e :: es ≠ [] := by simp
          change ons_turnPow d e +
              ons_openTurnSum ((e :: es) ++ r) = _
          rw [ih htail, ons_openTurnSum_cons_cons]
          simp [List.getLast!]
          abel

theorem ons_openTurnSum_replicate (n : ℕ) (d : Fin 4) :
    ons_openTurnSum (List.replicate n d) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          simp only [List.replicate_succ, ons_openTurnSum_cons_cons,
            ons_turnPow]
          norm_num
          simpa only [List.replicate_succ] using ih

@[simp] theorem ons_getLast_replicate_succ
    (n : ℕ) (d : Fin 4) :
    (List.replicate (n + 1) d).getLast! = d := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      simp [List.getLast!]

@[simp] theorem ons_getLast?_replicate_succ_getD
    (n : ℕ) (d : Fin 4) :
    (List.replicate (n + 1) d).getLast?.getD 0 = d := by
  rw [List.getLast?_replicate]
  simp

@[simp] theorem ons_head_replicate_succ
    (n : ℕ) (d : Fin 4) :
    (List.replicate (n + 1) d).head! = d := by
  rw [List.replicate_succ]
  rfl

theorem ons_pathDisplacement_replicate (n : ℕ) (d : Fin 4) :
    ons_pathDisplacement (List.replicate n d) = n • stepOf d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, ons_pathDisplacement_cons, ih]
      rw [add_comm]
      exact (succ_nsmul (stepOf d) n).symm

theorem ons_pathVertices_replicate (n : ℕ) (d : Fin 4) :
    ons_pathVertices (List.replicate n d) =
      (List.range (n + 1)).map (fun k ↦ k • stepOf d) := by
  induction n with
  | zero => simp [ons_pathVertices]
  | succ n ih =>
      rw [List.replicate_succ, ons_pathVertices_cons, ih]
      conv_rhs => rw [show n + 1 + 1 = (n + 1) + 1 by rfl,
        List.range_succ_eq_map]
      simp only [List.map_map, List.map_cons, zero_nsmul,
        List.cons.injEq, true_and]
      apply List.map_congr_left
      intro k hk
      simp only [Function.comp_apply]
      rw [succ_nsmul]
      abel

theorem ons_mem_pathVertices_replicate_iff
    (n : ℕ) (d : Fin 4) (z : ℤ × ℤ) :
    z ∈ ons_pathVertices (List.replicate n d) ↔
      ∃ k : ℕ, k ≤ n ∧ z = k • stepOf d := by
  rw [ons_pathVertices_replicate, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Nat.le_of_lt_succ (List.mem_range.mp hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mpr (Nat.lt_succ_iff.mpr hk), rfl⟩

theorem ons_pathVertices_replicate_dropLast
    (n : ℕ) (d : Fin 4) :
    (ons_pathVertices (List.replicate n d)).dropLast =
      (List.range n).map (fun k ↦ k • stepOf d) := by
  rw [ons_pathVertices_replicate, List.range_succ,
    List.map_append, List.dropLast_append_of_ne_nil (by simp)]
  simp

theorem ons_map_pathVertices_replicate_dropLast
    {X : Type*} (f : (ℤ × ℤ) → X) (n : ℕ) (d : Fin 4) :
    (List.map f (ons_pathVertices (List.replicate n d))).dropLast =
      (List.range n).map (fun k ↦ f (k • stepOf d)) := by
  rw [← List.map_dropLast, ons_pathVertices_replicate_dropLast,
    List.map_map]
  simp [Function.comp_def]

theorem ons_mem_pathVertices_replicate_dropLast_iff
    (n : ℕ) (d : Fin 4) (z : ℤ × ℤ) :
    z ∈ (ons_pathVertices (List.replicate n d)).dropLast ↔
      ∃ k : ℕ, k < n ∧ z = k • stepOf d := by
  rw [ons_pathVertices_replicate_dropLast, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mpr hk, rfl⟩

end StatMech.Onsager
