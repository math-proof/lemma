import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma w2aux_mem_smul_top [Fintype n] [DecidableEq n] [CommRing A] {I : Ideal A} {M : Matrix n n A} (hM : ∀ i j, M i j ∈ I) : M ∈ (I • ⊤ : Submodule A (Matrix n n A)) := by
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have hsingle : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : A) := by rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hsingle]
  apply Submodule.smul_mem_smul (hM i j) Submodule.mem_top

private lemma w2aux_exists_map_eq [CommRing A] [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)} (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) (X : Matrix n n k) : ∃ Y ∈ Submodule.span A S, Y.map π = X := by
  have hX : X ∈ Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) := hS ▸ Submodule.mem_top
  induction hX using Submodule.span_induction
  ·
    rename_i x hx
    obtain ⟨Y, hY, rfl⟩ := hx
    exact ⟨Y, Submodule.subset_span hY, rfl⟩
  ·
    exact ⟨0, Submodule.zero_mem _, by simp [Matrix.map_zero]⟩
  ·
    rename_i x y _ _ hx hy
    obtain ⟨Y, hY, rfl⟩ := hx
    obtain ⟨Z, hZ, rfl⟩ := hy
    exact ⟨Y + Z, Submodule.add_mem _ hY hZ, by simp [Matrix.map_add]⟩
  ·
    rename_i c x _ hx
    obtain ⟨Y, hY, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hπ c
    refine ⟨c' • Y, Submodule.smul_mem _ _ hY, ?_⟩
    ext i j
    simp [Matrix.map_apply]

private lemma w2aux_span_lift [Fintype n] [DecidableEq n] [CommRing A] [IsLocalRing A] [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)} (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) : Submodule.span A S = ⊤ := by
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) Module.Finite.fg_top (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
  intro Z _
  obtain ⟨Y, hY, hYZ⟩ := w2aux_exists_map_eq π hπ hS (Z.map π)
  have hZY : Z - Y ∈ (maximalIdeal A • ⊤ : Submodule A (Matrix n n A)) := by
    refine w2aux_mem_smul_top fun i j => ?_
    have hker : ∀ a : A, π a = 0 → a ∈ maximalIdeal A := fun a ha => by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro h
      apply not_isUnit_zero (ha ▸ h.map π)
    refine hker _ ?_
    have := congrArg (fun W => W i j) hYZ
    simp [Matrix.map_apply] at this
    simp [this]
  have : Z = Y + (Z - Y) := by abel
  rw [this]
  apply Submodule.add_mem _ (Submodule.mem_sup_left hY) (Submodule.mem_sup_right hZY)

private lemma w2aux_center [Fintype n] [DecidableEq n] [CommRing A] {S : Set (Matrix n n A)} (hS : Submodule.span A S = ⊤) (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) : ∃ a : A, M = a • 1 := by
  have hadd {X Y : Matrix n n A} (hX : X ∈ {X | X * M = M * X}) (hY : Y ∈ {X | X * M = M * X}) : X + Y ∈ {X | X * M = M * X} := by
    simp [Set.mem_ofPred_eq] at hX hY ⊢
    rw [add_mul, mul_add, hX, hY]
  have hzero : (0 : Matrix n n A) ∈ {X | X * M = M * X} := by simp [Set.mem_ofPred_eq]
  have hsmul (a : A) {X : Matrix n n A} (hX : X ∈ {X | X * M = M * X}) : a • X ∈ {X | X * M = M * X} := by
    simp [Set.mem_ofPred_eq] at hX ⊢
    rw [hX]
  let C : Submodule A (Matrix n n A) := { carrier := {X | X * M = M * X}, add_mem' := hadd, zero_mem' := hzero, smul_mem' := hsmul }
  have hcomm : ∀ X : Matrix n n A, X * M = M * X := by
    have hle : Submodule.span A S ≤ C := by
      refine Submodule.span_le.mpr fun X hX => ?_
      simpa [C, Set.mem_ofPred_eq] using hM X hX
    intro X
    have hXC : X ∈ C := hle (hS ▸ Submodule.mem_top)
    simpa [C, Set.mem_ofPred_eq] using hXC
  have hMc : M ∈ Set.center (Matrix n n A) := Semigroup.mem_center_iff.mpr hcomm
  rw [Matrix.center_eq_range] at hMc
  obtain ⟨a, ha⟩ := hMc
  refine ⟨a, ?_⟩
  rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/--
[Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_eq_smul_one_of_commute_of_map_span_eq_top.lean)
-/
@[path]
private lemma main
  [Fintype n] [DecidableEq n]
  [CommRing A] [IsLocalRing A]
  [Field k]
  (π : A →+* k) (hπ : Function.Surjective π)
  {S : Set (Matrix n n A)}
  (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤)
  (M : Matrix n n A) (hM : ∀ X ∈ S, X * M = M * X) :
  -- imply
  ∃ a : A, M = a • 1 :=
  w2aux_center (w2aux_span_lift π hπ hS) M hM


-- created on 2026-10-20
