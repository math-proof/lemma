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
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part7


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCSSourceBelow_displacement (R : ℕ) :
    ons_pathDisplacement (hexCSSourceBelow R) = ((R : ℤ), (R : ℤ)) := by
  ext <;> simp [hexCSSourceBelow, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk] <;> omega

theorem hexCSSourceAbove_displacement (R : ℕ) :
    ons_pathDisplacement (hexCSSourceAbove R) = ((R : ℤ), -(R : ℤ)) := by
  ext <;> simp [hexCSSourceAbove, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk] <;> omega

theorem hexCSEastTail_displacement (R : ℕ) (dx : ℤ)
    (h : dx ≤ R) :
    ons_pathDisplacement (hexCSEastTail R dx) =
      ((R : ℤ) + 1 - dx, 0) := by
  simp [hexCSEastTail, ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) + 1 - dx)]

theorem hexCSSouthEastTail_displacement (R : ℕ) (dx dy : ℤ)
    (hx : dx ≤ R) (hy : -(R : ℤ) ≤ dy) :
    ons_pathDisplacement (hexCSSouthEastTail R dx dy) =
      ((R : ℤ) + 1 - dx, -((R : ℤ) + dy)) := by
  ext <;> simp [hexCSSouthEastTail, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk,
    Int.toNat_of_nonneg (by omega : 0 ≤ dy + R),
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) + 1 - dx)] <;> omega

theorem hexCSWestNorthEastTail_displacement
    (R : ℕ) (dx dy : ℤ)
    (hx : -(R : ℤ) ≤ dx) (hy : dy ≤ R) :
    ons_pathDisplacement (hexCSWestNorthEastTail R dx dy) =
      ((R : ℤ) + 1 - dx, (R : ℤ) - dy) := by
  ext <;> simp [hexCSWestNorthEastTail, ons_pathDisplacement_append,
    ons_pathDisplacement_replicate, StatMech.Onsager.BaseCase.stepOf,
    Prod.smul_mk,
    Int.toNat_of_nonneg (by omega : 0 ≤ dx + R),
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) - dy)] <;> omega

theorem hexCS_openTurn_three_replicates
    (a b c : Fin 4) (na nb nc : ℕ) :
    ons_openTurnSum (List.replicate (na + 1) a ++
      List.replicate (nb + 1) b ++ List.replicate (nc + 1) c) =
      ons_turnPow a b + ons_turnPow b c := by
  rw [List.append_assoc,
    ons_openTurnSum_append (List.replicate (na + 1) a)
      (List.replicate (nb + 1) b ++ List.replicate (nc + 1) c)
      (by simp) (by simp),
    ons_openTurnSum_append (List.replicate (nb + 1) b)
      (List.replicate (nc + 1) c) (by simp) (by simp)]
  simp [ons_openTurnSum_replicate]

theorem hexCS_openTurn_two_replicates
    (a b : Fin 4) (na nb : ℕ) :
    ons_openTurnSum (List.replicate (na + 1) a ++
      List.replicate (nb + 1) b) = ons_turnPow a b := by
  rw [ons_openTurnSum_append _ _ (by simp) (by simp)]
  simp [ons_openTurnSum_replicate]

theorem hexCSSourceBelow_openTurn (R : ℕ) (hR : 0 < R) :
    ons_openTurnSum (hexCSSourceBelow R) = 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  have h := hexCS_openTurn_three_replicates 0 1 2 (2 * r + 1) r r
  norm_num [hexCSSourceBelow, ons_turnPow] at h ⊢
  simpa [show 2 * (r + 1) = 2 * r + 2 by omega] using h

theorem hexCSSourceAbove_openTurn (R : ℕ) (hR : 0 < R) :
    ons_openTurnSum (hexCSSourceAbove R) = -2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R ≠ 0)
  have h := hexCS_openTurn_three_replicates 0 3 2 (2 * r + 1) r r
  norm_num [hexCSSourceAbove, ons_turnPow] at h ⊢
  simpa [show 2 * (r + 1) = 2 * r + 2 by omega] using h

theorem hexCSEastTail_openTurn (R : ℕ) (dx : ℤ) :
    ons_openTurnSum (hexCSEastTail R dx) = 0 := by
  exact ons_openTurnSum_replicate _ _

theorem hexCSWestNorthEastTail_openTurn
    (R : ℕ) (dx dy : ℤ)
    (hW : 0 < dx + R) (hN : 0 < (R : ℤ) - dy) :
    ons_openTurnSum (hexCSWestNorthEastTail R dx dy) = -2 := by
  obtain ⟨w, hw⟩ : ∃ w, (dx + R).toNat = w + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) - dy).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 2 * R + 1 = r + 1 := by
    exact ⟨2 * R, rfl⟩
  have h := hexCS_openTurn_three_replicates 2 1 0 w n r
  norm_num [ons_turnPow] at h ⊢
  simpa [hexCSWestNorthEastTail, hw, hn, hr] using h

theorem hexCSSouthEastTail_openTurn
    (R : ℕ) (dx dy : ℤ)
    (hS : 0 < dy + R) (hE : 0 < (R : ℤ) - dx) :
    ons_openTurnSum (hexCSSouthEastTail R dx dy) = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, (dy + R).toNat = s + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨r, hr⟩ : ∃ r, ((R : ℤ) + 1 - dx).toNat = r + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hzero
    have hz := Int.toNat_eq_zero.mp hzero
    omega
  have h := hexCS_openTurn_two_replicates 3 0 s r
  norm_num [ons_turnPow] at h ⊢
  simpa [hexCSSouthEastTail, hs, hr] using h

theorem hexCSSourceBelow_vertices_dropLast_nodup (R : ℕ) :
    (ons_pathVertices (hexCSSourceBelow R)).dropLast.Nodup := by
  rw [hexCSSourceBelow, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSSourceAbove_vertices_dropLast_nodup (R : ℕ) :
    (ons_pathVertices (hexCSSourceAbove R)).dropLast.Nodup := by
  rw [hexCSSourceAbove, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSSourceBelow_vertex_cases
    (R : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast) :
    (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ), (k : ℤ))) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ) - (k : ℤ), (R : ℤ))) := by
  rw [hexCSSourceBelow, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast] at hz
  simp only [ons_pathVertices_replicate_dropLast] at hz
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] at hz ⊢
  rcases hz with hz | hz | hz
  · left
    simpa only [eq_comm] using hz
  · right; left
    simpa only [eq_comm] using hz
  · right; right
    obtain ⟨k, hk, rfl⟩ := hz
    exact ⟨k, hk, by ext <;> simp <;> ring⟩

theorem hexCSSourceAbove_vertex_cases
    (R : ℕ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast) :
    (∃ k : ℕ, k < 2 * R ∧ z = ((k : ℤ), 0)) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ), -(k : ℤ))) ∨
      (∃ k : ℕ, k < R ∧
        z = (2 * (R : ℤ) - (k : ℤ), -(R : ℤ))) := by
  rw [hexCSSourceAbove, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast] at hz
  simp only [ons_pathVertices_replicate_dropLast] at hz
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] at hz ⊢
  rcases hz with hz | hz | hz
  · left
    simpa only [eq_comm] using hz
  · right; left
    obtain ⟨k, hk, hkz⟩ := hz
    exact ⟨k, hk, hkz.symm⟩
  · right; right
    obtain ⟨k, hk, hkz⟩ := hz
    exact ⟨k, hk, by rw [← hkz]; ext <;> simp <;> ring⟩

theorem hexCSEastTail_vertices_dropLast_nodup (R : ℕ) (dx : ℤ) :
    (ons_pathVertices (hexCSEastTail R dx)).dropLast.Nodup := by
  rw [hexCSEastTail, ons_pathVertices_replicate_dropLast]
  apply List.Nodup.map (by
    intro a b hab
    have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
    simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] at hx
    omega)
  exact List.nodup_range

theorem hexCSWestNorthEastTail_vertices_dropLast_nodup
    (R : ℕ) (dx dy : ℤ)
    (hW : 0 < dx + R) (hN : 0 < (R : ℤ) - dy) :
    (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast.Nodup := by
  rw [hexCSWestNorthEastTail, List.append_assoc,
    ons_pathVertices_append_dropLast,
    ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_append, List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append,
    Int.toNat_of_nonneg (by omega : 0 ≤ dx + R),
    Int.toNat_of_nonneg (by omega : 0 ≤ (R : ℤ) - dy)]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSSouthEastTail_vertices_dropLast_nodup
    (R : ℕ) (dx dy : ℤ)
    (hS : 0 < dy + R) :
    (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast.Nodup := by
  rw [hexCSSouthEastTail, ons_pathVertices_append_dropLast]
  simp only [ons_pathVertices_replicate_dropLast]
  simp only [List.map_map, Function.comp_apply]
  simp [ons_pathDisplacement_replicate,
    StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
    List.nodup_append,
    Int.toNat_of_nonneg (by omega : 0 ≤ dy + R)]
  repeat' apply And.intro
  all_goals
    first
    | apply List.Nodup.map (by
        intro a b hab
        have hx := congrArg (fun z : ℤ × ℤ => z.1) hab
        have hy := congrArg (fun z : ℤ × ℤ => z.2) hab
        simp [Function.comp_def] at hx hy
        omega)
      exact List.nodup_range
    | omega

theorem hexCSEastTail_endpoint_vertex_cases
    (R : ℕ) (dx dy : ℤ) (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast) :
    ∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧
      (dx, dy) + z = (dx + k, dy) := by
  obtain ⟨k, hk, hkz⟩ :=
    (ons_mem_pathVertices_replicate_dropLast_iff
      ((R : ℤ) + 1 - dx).toNat 0 z).mp (by
        simpa [hexCSEastTail] using hz)
  refine ⟨k, hk, ?_⟩
  rw [hkz]
  ext <;>
    simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] <;> ring

theorem hexCSWestNorthEastTail_endpoint_vertex_cases
    (R : ℕ) (dx dy : ℤ)
    (hx : 0 ≤ dx + R) (hy : 0 ≤ (R : ℤ) - dy)
    (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast) :
    (∃ k : ℕ, k < (dx + R).toNat ∧
        (dx, dy) + z = (dx - k, dy)) ∨
      (∃ k : ℕ, k < ((R : ℤ) - dy).toNat ∧
        (dx, dy) + z = (-(R : ℤ), dy + k)) ∨
      (∃ k : ℕ, k < 2 * R + 1 ∧
        (dx, dy) + z = (-(R : ℤ) + k, (R : ℤ))) := by
  let A := List.replicate (dx + R).toNat (2 : Fin 4)
  let B := List.replicate ((R : ℤ) - dy).toNat (1 : Fin 4)
  let C := List.replicate (2 * R + 1) (0 : Fin 4)
  have hshape : hexCSWestNorthEastTail R dx dy = A ++ (B ++ C) := by
    simp [hexCSWestNorthEastTail, A, B, C, List.append_assoc]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      A (B ++ C) z).mp hz with hwest | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dx + R).toNat 2 z).mp (by simpa [A] using hwest)
    refine ⟨k, hk, ?_⟩
    rw [hkz]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] <;> ring
  rcases (ons_mem_pathVertices_append_dropLast_iff
      B C z₁).mp hz₁ with hnorth | ⟨z₂, hz₂, ez₂⟩
  · right; left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        ((R : ℤ) - dy).toNat 1 z₁).mp (by simpa [B] using hnorth)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz,
      show ons_pathDisplacement A =
          (dx + R).toNat • StatMech.Onsager.BaseCase.stepOf 2 by
        simp [A, ons_pathDisplacement_replicate]]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        Int.toNat_of_nonneg hx] <;> ring
  · right; right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (2 * R + 1) 0 z₂).mp (by simpa [C] using hz₂)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, ez₂, hkz,
      show ons_pathDisplacement A =
          (dx + R).toNat • StatMech.Onsager.BaseCase.stepOf 2 by
        simp [A, ons_pathDisplacement_replicate],
      show ons_pathDisplacement B =
          ((R : ℤ) - dy).toNat •
            StatMech.Onsager.BaseCase.stepOf 1 by
        simp [B, ons_pathDisplacement_replicate]]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] <;> ring

theorem hexCSSouthEastTail_endpoint_vertex_cases
    (R : ℕ) (dx dy : ℤ) (hy : 0 ≤ dy + R)
    (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast) :
    (∃ k : ℕ, k < (dy + R).toNat ∧
        (dx, dy) + z = (dx, dy - k)) ∨
      (∃ k : ℕ, k < ((R : ℤ) + 1 - dx).toNat ∧
        (dx, dy) + z = (dx + k, -(R : ℤ))) := by
  let A := List.replicate (dy + R).toNat (3 : Fin 4)
  let B := List.replicate ((R : ℤ) + 1 - dx).toNat (0 : Fin 4)
  have hshape : hexCSSouthEastTail R dx dy = A ++ B := by
    simp [hexCSSouthEastTail, A, B]
  rw [hshape] at hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      A B z).mp hz with hsouth | ⟨z₁, hz₁, ez₁⟩
  · left
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        (dy + R).toNat 3 z).mp (by simpa [A] using hsouth)
    refine ⟨k, hk, ?_⟩
    rw [hkz]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk] <;> ring
  · right
    obtain ⟨k, hk, hkz⟩ :=
      (ons_mem_pathVertices_replicate_dropLast_iff
        ((R : ℤ) + 1 - dx).toNat 0 z₁).mp (by simpa [B] using hz₁)
    refine ⟨k, hk, ?_⟩
    rw [ez₁, hkz,
      show ons_pathDisplacement A =
          (dy + R).toNat • StatMech.Onsager.BaseCase.stepOf 3 by
        simp [A, ons_pathDisplacement_replicate]]
    ext <;>
      simp [StatMech.Onsager.BaseCase.stepOf, Prod.smul_mk,
        Int.toNat_of_nonneg hy] <;> ring


theorem hexCSEndDelta_left_sign
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hc : e.vtx.1.color = .black) (hedge : e.edge = 0) :
    (0 ≤ hexAWTrans e.vtx.1 → 0 < (hexCSEndDelta e).2) ∧
      (¬ 0 ≤ hexAWTrans e.vtx.1 →
        (hexCSEndDelta e).2 < 0) := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWTrans, hexAWDepth, hexAWLong] at hc hedge hb ⊢
  constructor <;> intro hs
  · by_contra hstrict
    have hzero : i = 0 ∧ j = 0 := by omega
    apply hne
    rw [HexIncidence.mk.injEq]
    constructor
    · apply Subtype.ext
      simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord,
        hzero.1, hzero.2]
    · rfl
  · omega

theorem hexCSEndDelta_slant_sign
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (e.vtx.1.color = .white ∧ e.edge = 1 →
        0 < (hexCSEndDelta e).2) ∧
      (e.vtx.1.color = .white ∧ e.edge = 2 →
        (hexCSEndDelta e).2 < 0) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hc hb ⊢ <;> omega

theorem hexCSEndDelta_right_zero_height
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hc : e.vtx.1.color = .white) (hedge : e.edge = 0)
    (hy : (hexCSEndDelta e).2 = 0) :
    (hexCSEndDelta e).1 < 0 := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong] at hc hedge hb hy ⊢ <;>
    omega


theorem hexCSEastRay_not_inside
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hside :
      (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L))
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (k : ℕ) :
    hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠
      hexCSEndDelta e + ((k : ℤ), 0) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rcases c with ⟨a, b, ccolor⟩
  cases color <;> fin_cases edge <;> cases ccolor <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong, hexCSInStrip,
      hexAWBookRe2] at hside hc ⊢ <;> omega


theorem hexCSWestRay_not_inside
    {T L : ℕ} (e : HexCSIncidence T L)
    (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = T)
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (k : ℕ) :
    hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠
      hexCSEndDelta e + (-(k : ℤ), 0) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rcases c with ⟨a, b, ccolor⟩
  cases color <;> fin_cases edge <;> cases ccolor <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong, hexCSInStrip,
      hexAWBookRe2] at hside hc ⊢ <;> omega


theorem hexCSSouthRay_not_inside
    {T L : ℕ} (e : HexCSIncidence T L)
    (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧
      e.vtx.1.j = L)
    (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) (k : ℕ) :
    hexBrickPos c - hexBrickPos hexCSOutsideStartCoord ≠
      hexCSEndDelta e + (0, -(k : ℤ)) := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rcases c with ⟨a, b, ccolor⟩
  cases color <;> fin_cases edge <;> cases ccolor <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong, hexCSInStrip,
      hexAWBookRe2] at hside hc ⊢ <;> omega


theorem hexCS_three_piece_x_slab
    (P C S : List (Fin 4)) (D : ℤ)
    (hP : ∀ p ∈ (ons_pathVertices P).dropLast,
      0 ≤ p.1 ∧ p.1 < D)
    (hC : ∀ c ∈ (ons_pathVertices C).dropLast,
      0 ≤ (ons_pathDisplacement P + c).1 ∧
        (ons_pathDisplacement P + c).1 < D)
    (hS : ∀ s ∈ (ons_pathVertices S).dropLast,
      0 ≤ (ons_pathDisplacement P +
          ons_pathDisplacement C + s).1 ∧
        (ons_pathDisplacement P + ons_pathDisplacement C + s).1 < D) :
    ∀ z ∈ (ons_pathVertices (P ++ C ++ S)).dropLast,
      0 ≤ z.1 ∧ z.1 < D := by
  intro z hz
  rcases (ons_mem_pathVertices_append_dropLast_iff
      (P ++ C) S z).mp hz with hpc | ⟨s, hs, rfl⟩
  · rcases (ons_mem_pathVertices_append_dropLast_iff
        P C z).mp hpc with hp | ⟨c, hc, rfl⟩
    · exact hP z hp
    · exact hC c hc
  · rw [ons_pathDisplacement_append]
    exact hS s hs

theorem hexCSSourceBelow_x_slab (R : ℕ) :
    ∀ p ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast,
      0 ≤ p.1 ∧ p.1 < (2 * R + 1 : ℕ) := by
  intro p hp
  rcases hexCSSourceBelow_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    simp <;> omega

theorem hexCSSourceAbove_x_slab (R : ℕ) :
    ∀ p ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast,
      0 ≤ p.1 ∧ p.1 < (2 * R + 1 : ℕ) := by
  intro p hp
  rcases hexCSSourceAbove_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    simp <;> omega

theorem hexCS_central_x_slab
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    let R := hexCSBrickRadius T L
    ∀ c ∈ (ons_pathVertices
      (hexCSBrickDirections 1 ts)).dropLast,
      0 ≤ (((R : ℤ), 0) + c).1 ∧
        (((R : ℤ), 0) + c).1 < (((2 * R + 1 : ℕ) : ℤ)) := by
  dsimp only
  let R := hexCSBrickRadius T L
  intro c hc
  rcases hexCSBrickDirections_dropLast_mem_cases
      e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
  · simp
    have hR : 0 < (R : ℤ) := by
      dsimp [R, hexCSBrickRadius]
      omega
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) <
          (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 ∧
        (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2 < R) at hb
    change 0 ≤ (R : ℤ) + qx ∧
      (R : ℤ) + qx < 2 * R + 1
    omega

theorem hexCSEastTail_x_slab
    (R : ℕ) (dx dy : ℤ)
    (hxlo : -(R : ℤ) < dx) (hxhi : dx < R) :
    ∀ s ∈ (ons_pathVertices (hexCSEastTail R dx)).dropLast,
      0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧
        (((R : ℤ), 0) + (dx, dy) + s).1 <
          (((2 * R + 1 : ℕ) : ℤ)) := by
  intro s hs
  obtain ⟨k, hk, hkz⟩ :=
    hexCSEastTail_endpoint_vertex_cases R dx dy s hs
  have hlen : 0 ≤ (R : ℤ) + 1 - dx := by omega
  have hk' : (k : ℤ) <
      ((((R : ℤ) + 1 - dx).toNat : ℕ) : ℤ) := by
    exact_mod_cast hk
  rw [Int.toNat_of_nonneg hlen] at hk'
  rw [add_assoc, hkz]
  simp
  omega

theorem hexCSWestNorthEastTail_x_slab
    (R : ℕ) (dx dy : ℤ)
    (hxlo : -(R : ℤ) < dx) (hxhi : dx < R)
    (hyhi : dy < R) :
    ∀ s ∈ (ons_pathVertices
      (hexCSWestNorthEastTail R dx dy)).dropLast,
      0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧
        (((R : ℤ), 0) + (dx, dy) + s).1 <
          (((2 * R + 1 : ℕ) : ℤ)) := by
  intro s hs
  have hx : 0 ≤ dx + R := by omega
  have hy : 0 ≤ (R : ℤ) - dy := by omega
  rcases hexCSWestNorthEastTail_endpoint_vertex_cases
      R dx dy hx hy s hs with
      ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
  · have hk' : (k : ℤ) < (((dx + R).toNat : ℕ) : ℤ) := by
      exact_mod_cast hk
    rw [Int.toNat_of_nonneg hx] at hk'
    rw [add_assoc, hkz]
    simp
    omega
  · rw [add_assoc, hkz]
    simp
  · rw [add_assoc, hkz]
    simp
    omega

theorem hexCSSouthEastTail_x_slab
    (R : ℕ) (dx dy : ℤ)
    (hxlo : -(R : ℤ) < dx) (hxhi : dx < R)
    (hylo : -(R : ℤ) < dy) :
    ∀ s ∈ (ons_pathVertices
      (hexCSSouthEastTail R dx dy)).dropLast,
      0 ≤ (((R : ℤ), 0) + (dx, dy) + s).1 ∧
        (((R : ℤ), 0) + (dx, dy) + s).1 <
          (((2 * R + 1 : ℕ) : ℤ)) := by
  intro s hs
  have hy : 0 ≤ dy + R := by omega
  rcases hexCSSouthEastTail_endpoint_vertex_cases
      R dx dy hy s hs with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
  · rw [add_assoc, hkz]
    simp
    omega
  · have hlen : 0 ≤ (R : ℤ) + 1 - dx := by omega
    have hk' : (k : ℤ) <
        ((((R : ℤ) + 1 - dx).toNat : ℕ) : ℤ) := by
      exact_mod_cast hk
    rw [Int.toNat_of_nonneg hlen] at hk'
    rw [add_assoc, hkz]
    simp
    omega


theorem hexCS_three_piece_vertices_dropLast_nodup
    (P C S : List (Fin 4))
    (hP : (ons_pathVertices P).dropLast.Nodup)
    (hC : (ons_pathVertices C).dropLast.Nodup)
    (hS : (ons_pathVertices S).dropLast.Nodup)
    (hPC : ∀ p ∈ (ons_pathVertices P).dropLast,
      ∀ c ∈ (ons_pathVertices C).dropLast,
        p ≠ ons_pathDisplacement P + c)
    (hPS : ∀ p ∈ (ons_pathVertices P).dropLast,
      ∀ s ∈ (ons_pathVertices S).dropLast,
        p ≠ ons_pathDisplacement P +
          ons_pathDisplacement C + s)
    (hCS : ∀ c ∈ (ons_pathVertices C).dropLast,
      ∀ s ∈ (ons_pathVertices S).dropLast,
        ons_pathDisplacement P + c ≠
          ons_pathDisplacement P + ons_pathDisplacement C + s) :
    (ons_pathVertices (P ++ C ++ S)).dropLast.Nodup := by
  rw [ons_pathVertices_append_dropLast (P ++ C) S,
    ons_pathVertices_append_dropLast P C,
    ons_pathDisplacement_append]
  have hC' : ((ons_pathVertices C).dropLast.map
      (ons_pathDisplacement P + ·)).Nodup :=
    hC.map (add_right_injective _)
  have hS' : ((ons_pathVertices S).dropLast.map
      (ons_pathDisplacement P + ons_pathDisplacement C + ·)).Nodup :=
    hS.map (add_right_injective _)
  have hPC' : ((ons_pathVertices P).dropLast ++
      (ons_pathVertices C).dropLast.map
        (ons_pathDisplacement P + ·)).Nodup := by
    apply List.Nodup.append hP hC'
    rw [List.disjoint_iff_ne]
    intro p hp q hq
    rw [List.mem_map] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact hPC p hp c hc
  apply List.Nodup.append hPC' hS'
  rw [List.disjoint_iff_ne]
  intro q hq r hr
  rw [List.mem_append] at hq
  rw [List.mem_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  rcases hq with hp | hc
  · exact hPS q hp s hs
  · rw [List.mem_map] at hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact hCS c hc s hs

theorem hexCSSourceBelow_central_disjoint
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    let R := hexCSBrickRadius T L
    ∀ p ∈ (ons_pathVertices (hexCSSourceBelow R)).dropLast,
      ∀ c ∈ (ons_pathVertices
        (hexCSBrickDirections 1 ts)).dropLast,
        p ≠ ons_pathDisplacement (hexCSSourceBelow R) + c := by
  dsimp only
  let R := hexCSBrickRadius T L
  intro p hp c hc
  rw [hexCSSourceBelow_displacement R]
  rcases hexCSSourceBelow_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases hexCSBrickDirections_dropLast_mem_cases
      e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
  · intro h
    change ((k : ℤ), 0) = ((R : ℤ), (R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    have hR : 0 < (R : ℤ) := by
      dsimp [R, hexCSBrickRadius]
      omega
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change ((k : ℤ), 0) = ((R : ℤ) + qx, (R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change (((2 * R : ℕ) : ℤ), (k : ℤ)) =
      ((R : ℤ), (R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change (((2 * R : ℕ) : ℤ), (k : ℤ)) =
      ((R : ℤ) + qx, (R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change ((2 * R : ℤ) - k, (R : ℤ)) =
      ((R : ℤ), (R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hd := hexCS_inside_brick_depth_pos q hq
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change 0 < qy - qx at hd
    intro h
    change ((2 * R : ℤ) - k, (R : ℤ)) =
      ((R : ℤ) + qx, (R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega

theorem hexCSSourceAbove_central_disjoint
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    let R := hexCSBrickRadius T L
    ∀ p ∈ (ons_pathVertices (hexCSSourceAbove R)).dropLast,
      ∀ c ∈ (ons_pathVertices
        (hexCSBrickDirections 1 ts)).dropLast,
        p ≠ ons_pathDisplacement (hexCSSourceAbove R) + c := by
  dsimp only
  let R := hexCSBrickRadius T L
  intro p hp c hc
  rw [hexCSSourceAbove_displacement R]
  rcases hexCSSourceAbove_vertex_cases R p hp with
      ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases hexCSBrickDirections_dropLast_mem_cases
      e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
  · intro h
    change ((k : ℤ), 0) = ((R : ℤ), -(R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    have hR : 0 < (R : ℤ) := by
      dsimp [R, hexCSBrickRadius]
      omega
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change ((k : ℤ), 0) = ((R : ℤ) + qx, -(R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change (((2 * R : ℕ) : ℤ), -(k : ℤ)) =
      ((R : ℤ), -(R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hb := hexCS_inside_brick_bounds q hq
    dsimp only at hb
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change (-(R : ℤ) < qx ∧ qx < R ∧
      -(R : ℤ) < qy ∧ qy < R) at hb
    intro h
    change (((2 * R : ℕ) : ℤ), -(k : ℤ)) =
      ((R : ℤ) + qx, -(R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega
  · intro h
    change ((2 * R : ℤ) - k, -(R : ℤ)) =
      ((R : ℤ), -(R : ℤ)) at h
    rw [Prod.mk.injEq] at h
    omega
  · have hd := hexCS_inside_brick_depth_pos q hq
    let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
    let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
    change 0 < qy - qx at hd
    intro h
    change ((2 * R : ℤ) - k, -(R : ℤ)) =
      ((R : ℤ) + qx, -(R : ℤ) + qy) at h
    rw [Prod.mk.injEq] at h
    omega


theorem hexCSBelowEastPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside :
      (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L))
    (hdy : 0 < (hexCSEndDelta e).2) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceBelow R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceBelow_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSEastTail_vertices_dropLast_nodup R dx
  · exact hexCSSourceBelow_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    rw [add_assoc, hkz]
    rcases hexCSSourceBelow_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      intro h
      have hy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp [dy] at hy
      omega
  · intro c hc s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    intro h
    have hcancel : c = (dx, dy) + s := by
      exact add_left_cancel (a := ((R : ℤ), (R : ℤ)))
        (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
    rcases hexCSBrickDirections_dropLast_mem_cases
        e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
    · rw [hkz] at hcancel
      have hy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
      simp [dy] at hy
      omega
    · apply hexCSEastRay_not_inside e he hside q hq k
      calc
        hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
            (dx, dy) + s := hcancel
        _ = (dx, dy) + ((k : ℤ), 0) := by
          simpa using hkz
        _ = hexCSEndDelta e + ((k : ℤ), 0) := by
          simp [dx, dy, Prod.ext_iff]

theorem hexCSAboveEastPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside :
      e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0)
    (hdy : (hexCSEndDelta e).2 < 0) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceAbove R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceAbove_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSEastTail_vertices_dropLast_nodup R dx
  · exact hexCSSourceAbove_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    rw [add_assoc, hkz]
    rcases hexCSSourceAbove_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      intro h
      have hy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp [dy] at hy
      omega
  · intro c hc s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    obtain ⟨k, hk, hkz⟩ :=
      hexCSEastTail_endpoint_vertex_cases R dx dy s hs
    change (dx, dy) + s = _ at hkz
    intro h
    have hcancel : c = (dx, dy) + s := by
      exact add_left_cancel (a := ((R : ℤ), -(R : ℤ)))
        (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
    rcases hexCSBrickDirections_dropLast_mem_cases
        e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
    · rw [hkz] at hcancel
      have hy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
      simp [dy] at hy
      omega
    · apply hexCSEastRay_not_inside e he (Or.inl hside) q hq k
      calc
        hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
            (dx, dy) + s := hcancel
        _ = (dx, dy) + ((k : ℤ), 0) := by
          simpa using hkz
        _ = hexCSEndDelta e + ((k : ℤ), 0) := by
          simp [dx, dy, Prod.ext_iff]

theorem hexCSRightPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = T) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceBelow R ++ C ++
        hexCSWestNorthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hzero : dy = 0 → dx < 0 := by
    intro hy
    exact hexCSEndDelta_right_zero_height (hT := hT) e he
      hside.1 hside.2.1 hy
  have hR : 0 < (R : ℤ) := by
    dsimp [R, hexCSBrickRadius]
    omega
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceBelow_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSWestNorthEastTail_vertices_dropLast_nodup
      R dx dy (by omega) (by omega)
  · exact hexCSSourceBelow_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hx : 0 ≤ dx + R := by omega
    have hy : 0 ≤ (R : ℤ) - dy := by omega
    rcases hexCSWestNorthEastTail_endpoint_vertex_cases
        R dx dy hx hy s hs with
        ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ <;>
      rcases hexCSSourceBelow_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      rw [add_assoc, hkz]
      intro h
      have hxx := congrArg (fun z : ℤ × ℤ => z.1) h
      have hyy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp at hxx hyy
      by_cases hy0 : dy = 0
      · have hdx := hzero hy0
        omega
      · omega
  · intro c hc s hs
    rw [hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hx : 0 ≤ dx + R := by omega
    have hy : 0 ≤ (R : ℤ) - dy := by omega
    rcases hexCSWestNorthEastTail_endpoint_vertex_cases
        R dx dy hx hy s hs with
        ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), (R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
      · rw [hkz] at hcancel
        have hxx := congrArg (fun z : ℤ × ℤ => z.1) hcancel
        have hyy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hxx hyy
        by_cases hy0 : dy = 0
        · have hdx := hzero hy0
          omega
        · omega
      · apply hexCSWestRay_not_inside e hside q hq k
        calc
          hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
              (dx, dy) + s := hcancel
          _ = (dx, dy) + (-(k : ℤ), 0) := by
            simpa using hkz
          _ = hexCSEndDelta e + (-(k : ℤ), 0) := by
            simp [dx, dy, Prod.ext_iff]
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), (R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rw [hkz] at hcancel
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hqmem, hqeq⟩
      · have hx0 := congrArg (fun z : ℤ × ℤ => z.1) hcancel
        simp at hx0
        omega
      · have hqbound := hexCS_inside_brick_bounds q hqmem
        dsimp only at hqbound
        let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
        let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
        change (-(R : ℤ) < qx ∧ qx < R ∧
          -(R : ℤ) < qy ∧ qy < R) at hqbound
        rw [hqeq] at hcancel
        change (qx, qy) = (-(R : ℤ), dy + k) at hcancel
        rw [Prod.mk.injEq] at hcancel
        omega
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), (R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rw [hkz] at hcancel
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hqmem, hqeq⟩
      · have hy0 := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hy0
        omega
      · have hqbound := hexCS_inside_brick_bounds q hqmem
        dsimp only at hqbound
        let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
        let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
        change (-(R : ℤ) < qx ∧ qx < R ∧
          -(R : ℤ) < qy ∧ qy < R) at hqbound
        rw [hqeq] at hcancel
        change (qx, qy) = (-(R : ℤ) + k, (R : ℤ)) at hcancel
        rw [Prod.mk.injEq] at hcancel
        omega

theorem hexCSLowerPeriod_vertices_dropLast_nodup
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧
      e.vtx.1.j = L) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    (ons_pathVertices
      (hexCSSourceAbove R ++ C ++
        hexCSSouthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2)).dropLast.Nodup := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hdy : dy < 0 :=
    (hexCSEndDelta_slant_sign e he).2 ⟨hside.1, hside.2.1⟩
  have hR : 0 < (R : ℤ) := by
    dsimp [R, hexCSBrickRadius]
    omega
  apply hexCS_three_piece_vertices_dropLast_nodup
  · exact hexCSSourceAbove_vertices_dropLast_nodup R
  · exact List.Nodup.sublist (List.dropLast_sublist _)
      (hexCSBrickDirections_vertices_nodup e ts he hne hadm)
  · exact hexCSSouthEastTail_vertices_dropLast_nodup
      R dx dy (by omega)
  · exact hexCSSourceAbove_central_disjoint e ts he hne hadm
  · intro p hp s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hy : 0 ≤ dy + R := by omega
    rcases hexCSSouthEastTail_endpoint_vertex_cases
        R dx dy hy s hs with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩ <;>
      rcases hexCSSourceAbove_vertex_cases R p hp with
        ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    all_goals
      rw [add_assoc, hkz]
      intro h
      have hxx := congrArg (fun z : ℤ × ℤ => z.1) h
      have hyy := congrArg (fun z : ℤ × ℤ => z.2) h
      simp at hxx hyy
      omega
  · intro c hc s hs
    rw [hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm]
    have hy : 0 ≤ dy + R := by omega
    rcases hexCSSouthEastTail_endpoint_vertex_cases
        R dx dy hy s hs with ⟨k, hk, hkz⟩ | ⟨k, hk, hkz⟩
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), -(R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hq, rfl⟩
      · rw [hkz] at hcancel
        have hyy := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hyy
        omega
      · apply hexCSSouthRay_not_inside e hside q hq k
        calc
          hexBrickPos q - hexBrickPos hexCSOutsideStartCoord =
              (dx, dy) + s := hcancel
          _ = (dx, dy) + (0, -(k : ℤ)) := by
            simpa using hkz
          _ = hexCSEndDelta e + (0, -(k : ℤ)) := by
            simp [dx, dy, Prod.ext_iff]
    · intro h
      have hcancel : c = (dx, dy) + s :=
        add_left_cancel (a := ((R : ℤ), -(R : ℤ)))
          (by simpa [dx, dy, add_assoc, Prod.ext_iff] using h)
      rw [hkz] at hcancel
      rcases hexCSBrickDirections_dropLast_mem_cases
          e ts he hne hadm c hc with rfl | ⟨q, hqmem, hqeq⟩
      · have hy0 := congrArg (fun z : ℤ × ℤ => z.2) hcancel
        simp at hy0
        omega
      · have hqbound := hexCS_inside_brick_bounds q hqmem
        dsimp only at hqbound
        let qx := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).1
        let qy := (hexBrickPos q - hexBrickPos hexCSOutsideStartCoord).2
        change (-(R : ℤ) < qx ∧ qx < R ∧
          -(R : ℤ) < qy ∧ qy < R) at hqbound
        rw [hqeq] at hcancel
        change (qx, qy) = (dx + k, -(R : ℤ)) at hcancel
        rw [Prod.mk.injEq] at hcancel
        omega


theorem hexCSBelowEastPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside :
      (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L))
    (hdy : 0 < (hexCSEndDelta e).2) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceBelow R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let l := hexCSSourceBelow R ++ C ++ hexCSEastTail R dx
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (R + dy)
  · dsimp [l]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSEastTail_displacement R dx (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSBelowEastPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside hdy
  · dsimp [l]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceBelow_x_slab R
    · intro c hc
      rw [hexCSSourceBelow_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceBelow_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSEastTail_x_slab R dx dy hb.1 hb.2.1 s hs

theorem hexCSAboveEastPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .black ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = 0)
    (hdy : (hexCSEndDelta e).2 < 0) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceAbove R ++ C ++
        hexCSEastTail R (hexCSEndDelta e).1) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let l := hexCSSourceAbove R ++ C ++ hexCSEastTail R dx
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (-R + dy)
  · dsimp [l]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSEastTail_displacement R dx (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSAboveEastPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside hdy
  · dsimp [l]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceAbove_x_slab R
    · intro c hc
      rw [hexCSSourceAbove_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceAbove_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSEastTail_x_slab R dx dy hb.1 hb.2.1 s hs

theorem hexCSRightPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 0 ∧
      hexAWDepth e.vtx.1 = T) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceBelow R ++ C ++
        hexCSWestNorthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let S := hexCSWestNorthEastTail R dx dy
  let l := hexCSSourceBelow R ++ C ++ S
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (2 * R)
  · dsimp [l, S]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceBelow_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSWestNorthEastTail_displacement R dx dy
        (by omega) (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSRightPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside
  · dsimp [l, S]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceBelow_x_slab R
    · intro c hc
      rw [hexCSSourceBelow_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceBelow_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSWestNorthEastTail_x_slab R dx dy
          hb.1 hb.2.1 hb.2.2.2 s hs

theorem hexCSLowerPeriod_cyclicTurnSum_eq_zero
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hside : e.vtx.1.color = .white ∧ e.edge = 2 ∧
      e.vtx.1.j = L) :
    let R := hexCSBrickRadius T L
    let C := hexCSBrickDirections 1 ts
    ons_cyclicTurnSum
      (hexCSSourceAbove R ++ C ++
        hexCSSouthEastTail R (hexCSEndDelta e).1
          (hexCSEndDelta e).2) = 0 := by
  dsimp only
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  let S := hexCSSouthEastTail R dx dy
  let l := hexCSSourceAbove R ++ C ++ S
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  letI : NeZero l.length := ⟨by simp [l, hC]⟩
  apply hexCS_cyclicTurnSum_eq_zero_of_slab l
    (2 * R + 1) (-2 * R)
  · dsimp [l, S]
    rw [ons_pathDisplacement_append,
      ons_pathDisplacement_append,
      hexCSSourceAbove_displacement,
      hexCSBrickDirections_displacement e ts he hne hadm,
      hexCSSouthEastTail_displacement R dx dy
        (by omega) (by omega)]
    ext <;> simp [dx, dy] <;> omega
  · omega
  · exact hexCSLowerPeriod_vertices_dropLast_nodup
      e ts he hne hadm hside
  · dsimp [l, S]
    apply hexCS_three_piece_x_slab
    · exact hexCSSourceAbove_x_slab R
    · intro c hc
      rw [hexCSSourceAbove_displacement]
      simpa using hexCS_central_x_slab e ts he hne hadm c hc
    · intro s hs
      rw [hexCSSourceAbove_displacement,
        hexCSBrickDirections_displacement e ts he hne hadm]
      simpa [dx, dy] using
        hexCSSouthEastTail_x_slab R dx dy
          hb.1 hb.2.1 hb.2.2.1 s hs


theorem hexCSSourceBelow_ne_nil (R : ℕ) (hR : 0 < R) :
    hexCSSourceBelow R ≠ [] := by
  simp [hexCSSourceBelow, Nat.ne_of_gt hR]

theorem hexCSSourceAbove_ne_nil (R : ℕ) (hR : 0 < R) :
    hexCSSourceAbove R ≠ [] := by
  simp [hexCSSourceAbove, Nat.ne_of_gt hR]

theorem hexCSSourceBelow_head (R : ℕ) (hR : 0 < R) :
    (hexCSSourceBelow R).head! = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceBelow, show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
    List.replicate_succ]
  rfl

theorem hexCSSourceAbove_head (R : ℕ) (hR : 0 < R) :
    (hexCSSourceAbove R).head! = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceAbove, show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
    List.replicate_succ]
  rfl

theorem hexCSSourceBelow_getLast (R : ℕ) (hR : 0 < R) :
    (hexCSSourceBelow R).getLast! = 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceBelow,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp)]
  simp

theorem hexCSSourceAbove_getLast (R : ℕ) (hR : 0 < R) :
    (hexCSSourceAbove R).getLast! = 2 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  rw [hexCSSourceAbove,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp)]
  simp

theorem hexCSEastTail_ne_nil (R : ℕ) (dx : ℤ)
    (h : 0 < (R : ℤ) + 1 - dx) :
    hexCSEastTail R dx ≠ [] := by
  simp [hexCSEastTail, Int.toNat_eq_zero]
  omega

theorem hexCSEastTail_head (R : ℕ) (dx : ℤ)
    (h : 0 < (R : ℤ) + 1 - dx) :
    (hexCSEastTail R dx).head! = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) + 1 - dx).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSEastTail, hn]

theorem hexCSEastTail_getLast (R : ℕ) (dx : ℤ)
    (h : 0 < (R : ℤ) + 1 - dx) :
    (hexCSEastTail R dx).getLast! = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) + 1 - dx).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  rw [hexCSEastTail, hn]
  exact ons_getLast_replicate_succ n 0

theorem hexCSWestNorthEastTail_ne_nil
    (R : ℕ) (dx dy : ℤ) (hW : 0 < dx + R) :
    hexCSWestNorthEastTail R dx dy ≠ [] := by
  obtain ⟨n, hn⟩ : ∃ n, (dx + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSWestNorthEastTail, hn]

theorem hexCSWestNorthEastTail_head
    (R : ℕ) (dx dy : ℤ) (hW : 0 < dx + R) :
    (hexCSWestNorthEastTail R dx dy).head! = 2 := by
  obtain ⟨n, hn⟩ : ∃ n, (dx + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSWestNorthEastTail, hn]

theorem hexCSWestNorthEastTail_getLast
    (R : ℕ) (dx dy : ℤ) :
    (hexCSWestNorthEastTail R dx dy).getLast! = 0 := by
  rw [hexCSWestNorthEastTail,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp)]
  simp

theorem hexCSSouthEastTail_ne_nil
    (R : ℕ) (dx dy : ℤ) (hS : 0 < dy + R) :
    hexCSSouthEastTail R dx dy ≠ [] := by
  obtain ⟨n, hn⟩ : ∃ n, (dy + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSSouthEastTail, hn]

theorem hexCSSouthEastTail_head
    (R : ℕ) (dx dy : ℤ) (hS : 0 < dy + R) :
    (hexCSSouthEastTail R dx dy).head! = 3 := by
  obtain ⟨n, hn⟩ : ∃ n, (dy + R).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  simp [hexCSSouthEastTail, hn]

theorem hexCSSouthEastTail_getLast
    (R : ℕ) (dx dy : ℤ)
    (hE : 0 < (R : ℤ) + 1 - dx) :
    (hexCSSouthEastTail R dx dy).getLast! = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, ((R : ℤ) + 1 - dx).toNat = n + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    intro hz
    have := Int.toNat_eq_zero.mp hz
    omega
  rw [hexCSSouthEastTail,
    ons_getLast!_append_of_right_ne_nil _ _ (by simp [hn]), hn]
  exact ons_getLast_replicate_succ n 0


theorem hexCS_cyclicTurnSum_three_piece
    (P C S : List (Fin 4))
    (hP : P ≠ []) (hC : C ≠ []) (hS : S ≠ [])
    (hPhead : P.head! = 0) (hPlast : P.getLast! = 2)
    (hChead : C.head! = 2)
    (hjoin : C.getLast! = S.head!)
    (hSlast : S.getLast! = 0) :
    ons_cyclicTurnSum (P ++ C ++ S) =
      ons_openTurnSum P + ons_openTurnSum C + ons_openTurnSum S := by
  have hPC : P ++ C ≠ [] := List.append_ne_nil_of_right_ne_nil P hC
  have hl : P ++ C ++ S ≠ [] :=
    List.append_ne_nil_of_right_ne_nil (P ++ C) hS
  have hhead : (P ++ C ++ S).head! = P.head! := by
    simp [hP]
  have hlast : (P ++ C ++ S).getLast! = S.getLast! := by
    exact ons_getLast!_append_of_right_ne_nil (P ++ C) S hS
  have hPClast : (P ++ C).getLast! = C.getLast! :=
    ons_getLast!_append_of_right_ne_nil P C hC
  have hcyc : ons_cyclicTurnSum (P ++ C ++ S) =
      ons_openTurnSum (P ++ C ++ S) +
        ons_turnPow (P ++ C ++ S).getLast!
          (P ++ C ++ S).head! := by
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hl
    rw [hd]
    rfl
  rw [hcyc,
    ons_openTurnSum_append (P ++ C) S hPC hS,
    ons_openTurnSum_append P C hP hC,
    hPClast, hjoin, hhead, hlast,
    hPhead, hPlast, hChead, hSlast]
  norm_num [ons_turnPow]

end
end StatMech.Universality
