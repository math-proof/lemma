import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma w2aux_mem_smul_top {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] {I : Ideal A} {M : Matrix n n A} (hM : ∀ i j, M i j ∈ I) : M ∈ (I • ⊤ : Submodule A (Matrix n n A)) := by
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have hsingle : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hsingle]
  apply Submodule.smul_mem_smul (hM i j) Submodule.mem_top
private lemma w2aux_exists_map_eq {n A : Type*} [CommRing A] {k : Type*} [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)} (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) (X : Matrix n n k) : ∃ Y ∈ Submodule.span A S, Y.map π = X := by
  have hX : X ∈ Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) :=
    hS ▸ Submodule.mem_top
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
/--
[Matrix_span_eq_top_of_map_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_span_eq_top_of_map_span_eq_top.lean)
-/
@[path]
private lemma main
  [Fintype n] [DecidableEq n] [CommRing A] [IsLocalRing A]
  [Field k] (π : A →+* k) (hπ : Function.Surjective π) {S : Set (Matrix n n A)}
    (hS : Submodule.span k ((fun X : Matrix n n A => X.map π) '' S) = ⊤) :
    -- imply
    Submodule.span A S = ⊤ := by
    -- proof
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A) Module.Finite.fg_top
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
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
    simp only [Matrix.map_apply] at this
    simp [this]
  have : Z = Y + (Z - Y) := by abel
  rw [this]
  apply Submodule.add_mem _ (Submodule.mem_sup_left hY) (Submodule.mem_sup_right hZY)


-- created on 2026-10-20
