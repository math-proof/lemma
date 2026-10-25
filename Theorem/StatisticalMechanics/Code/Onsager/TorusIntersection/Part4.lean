/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.TorusIntersection.Part4


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_xSeamPortEdge_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_xSeamPortEdge L) := by
  intro y z h
  have hd := (ons_portEdge_eq_iff L
    (((-1 : ZMod L), z), 0)
    (((-1 : ZMod L), y), 0)).mp h
  rcases hd with hd | hd
  · exact congrArg (fun d : ons_Dart L => d.1.2) hd
  · have hdir := congrArg (fun d : ons_Dart L => d.2) hd
    simp [ons_dartRev] at hdir

theorem ons_ySeamPortEdge_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_ySeamPortEdge L) := by
  intro x z h
  have hd := (ons_portEdge_eq_iff L
    ((z, (-1 : ZMod L)), 1)
    ((x, (-1 : ZMod L)), 1)).mp h
  rcases hd with hd | hd
  · exact congrArg (fun d : ons_Dart L => d.1.1) hd
  · have hdir := congrArg (fun d : ons_Dart L => d.2) hd
    simp [ons_dartRev] at hdir

@[simp] theorem ons_xSeamEdge_xSeamPortEdge
    (L : ℕ) (y : ZMod L) :
    ons_xSeamEdge L (ons_xSeamPortEdge L y) := by
  refine ⟨y, ?_⟩
  simp [ons_xSeamPortEdge, ons_portEdge, ons_dirStep]

@[simp] theorem ons_ySeamEdge_ySeamPortEdge
    (L : ℕ) (x : ZMod L) :
    ons_ySeamEdge L (ons_ySeamPortEdge L x) := by
  refine ⟨x, ?_⟩
  simp [ons_ySeamPortEdge, ons_portEdge, ons_dirStep]

theorem ons_filter_xSeam_eq_image
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    F.filter (ons_xSeamEdge L) =
      (Finset.univ.filter
        (fun y : ZMod L => ons_xSeamPortEdge L y ∈ F)).image
          (ons_xSeamPortEdge L) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hedge, y, rfl⟩
    refine ⟨y, ?_, ?_⟩
    · rw [show ons_xSeamPortEdge L y =
        s(((0 : ZMod L), y), ((-1 : ZMod L), y)) by
          simp [ons_xSeamPortEdge, ons_portEdge, ons_dirStep]]
      exact hedge
    · simp [ons_xSeamPortEdge, ons_portEdge, ons_dirStep]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, ons_xSeamEdge_xSeamPortEdge L y⟩

theorem ons_filter_ySeam_eq_image
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    F.filter (ons_ySeamEdge L) =
      (Finset.univ.filter
        (fun x : ZMod L => ons_ySeamPortEdge L x ∈ F)).image
          (ons_ySeamPortEdge L) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hedge, x, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · rw [show ons_ySeamPortEdge L x =
        s((x, (0 : ZMod L)), (x, (-1 : ZMod L))) by
          simp [ons_ySeamPortEdge, ons_portEdge, ons_dirStep]]
      exact hedge
    · simp [ons_ySeamPortEdge, ons_portEdge, ons_dirStep]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, ons_ySeamEdge_ySeamPortEdge L x⟩

theorem ons_xFlux_neg_one_eq_seamCard
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ons_xFlux F (-1) =
      ((F.filter (ons_xSeamEdge L)).card : ZMod 2) := by
  classical
  unfold ons_xFlux
  calc
    (∑ y : ZMod L, ons_horizontalZBit F (-1, y)) =
        ∑ y : ZMod L,
          if ons_xSeamPortEdge L y ∈ F then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [ons_horizontalZBit, ons_horizontalBit, ons_edgeBit,
        ons_xSeamPortEdge]
      split <;> rfl
    _ = (((Finset.univ : Finset (ZMod L)).filter
          (fun y => ons_xSeamPortEdge L y ∈ F)).card : ZMod 2) := by
      simpa using (Finset.sum_boole
        (R := ZMod 2) (fun y : ZMod L => ons_xSeamPortEdge L y ∈ F)
        Finset.univ)
    _ = ((F.filter (ons_xSeamEdge L)).card : ZMod 2) := by
      rw [ons_filter_xSeam_eq_image L F,
        Finset.card_image_iff.mpr (ons_xSeamPortEdge_injective L).injOn]

theorem ons_yFlux_neg_one_eq_seamCard
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ons_yFlux F (-1) =
      ((F.filter (ons_ySeamEdge L)).card : ZMod 2) := by
  classical
  unfold ons_yFlux
  calc
    (∑ x : ZMod L, ons_verticalZBit F (x, -1)) =
        ∑ x : ZMod L,
          if ons_ySeamPortEdge L x ∈ F then (1 : ZMod 2) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [ons_verticalZBit, ons_verticalBit, ons_edgeBit,
        ons_ySeamPortEdge]
      split <;> rfl
    _ = (((Finset.univ : Finset (ZMod L)).filter
          (fun x => ons_ySeamPortEdge L x ∈ F)).card : ZMod 2) := by
      simpa using (Finset.sum_boole
        (R := ZMod 2) (fun x : ZMod L => ons_ySeamPortEdge L x ∈ F)
        Finset.univ)
    _ = ((F.filter (ons_ySeamEdge L)).card : ZMod 2) := by
      rw [ons_filter_ySeam_eq_image L F,
        Finset.card_image_iff.mpr (ons_ySeamPortEdge_injective L).injOn]

theorem ons_evenHomology_fst_cast_eq_xFlux
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((ons_evenHomology L F).1 : ZMod 2) = ons_xFlux F (-1) := by
  rw [ons_xFlux_neg_one_eq_seamCard]
  apply ZMod.val_injective 2
  rfl

theorem ons_evenHomology_snd_cast_eq_yFlux
    (L : ℕ) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((ons_evenHomology L F).2 : ZMod 2) = ons_yFlux F (-1) := by
  rw [ons_yFlux_neg_one_eq_seamCard]
  apply ZMod.val_injective 2
  rfl

theorem ons_sum_range_succ_first
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f i =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ∑ i ∈ Finset.range (n + 1 + 1), f i =
            (∑ i ∈ Finset.range (n + 1), f i) + f (n + 1) := by
          rw [Finset.sum_range_succ]
        _ = (f 0 + ∑ i ∈ Finset.range n, f (i + 1)) + f (n + 1) := by
          rw [ih]
        _ = f 0 + ∑ i ∈ Finset.range (n + 1), f (i + 1) := by
          rw [Finset.sum_range_succ]
          abel

theorem ons_sum_zmod_eq_sum_range
    {A : Type*} [AddCommMonoid A]
    (L : ℕ) [NeZero L] (f : ZMod L → A) :
    ∑ z : ZMod L, f z =
      ∑ i ∈ Finset.range L, f (i : ZMod L) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  change (∑ z : Fin (q + 1), f z) = _
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  apply congrArg f
  apply Fin.ext
  change i = i % (q + 1)
  exact (Nat.mod_eq_of_lt (Finset.mem_range.mp hi)).symm

end StatMech.Onsager
