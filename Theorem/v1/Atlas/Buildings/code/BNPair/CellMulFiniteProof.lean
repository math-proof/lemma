/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/CellMulFiniteProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.BNPair.Basic.Part2
import Mathlib.Tactic.Group
set_option linter.unusedSectionVars false

open scoped Classical

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}


namespace CellMulFinite

open BNPair

/-- Associativity of pointwise set multiplication: $(XY)Z = X(YZ)$. -/
theorem setMul_assoc (X Y Z : Set G) : setMul (setMul X Y) Z = setMul X (setMul Y Z) := by
  ext g
  simp only [setMul, Set.mem_setOf_eq]
  constructor
  · rintro ⟨xy, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩
    exact ⟨x, hx, y * z, ⟨y, hy, z, hz, rfl⟩, by group⟩
  · rintro ⟨x, hx, yz, ⟨y, hy, z, hz, rfl⟩, rfl⟩
    exact ⟨x * y, ⟨x, hx, y, hy, rfl⟩, z, hz, by group⟩

/-- Monotonicity of `setMul` in the left argument. -/
theorem setMul_mono_left {X₁ X₂ Y : Set G} (h : X₁ ⊆ X₂) :
    setMul X₁ Y ⊆ setMul X₂ Y := by
  intro g ⟨x, hx, y, hy, hg⟩
  exact ⟨x, h hx, y, hy, hg⟩

/-- Monotonicity of `setMul` in the right argument. -/
theorem setMul_mono_right {X Y₁ Y₂ : Set G} (h : Y₁ ⊆ Y₂) :
    setMul X Y₁ ⊆ setMul X Y₂ := by
  intro g ⟨x, hx, y, hy, hg⟩
  exact ⟨x, hx, y, h hy, hg⟩

/-- `setMul` distributes over a finite-indexed union on the left. -/
theorem setMul_biUnion_left {ι : Type*} (A : ι → Set G) (B : Set G) (F : Finset ι) :
    setMul (⋃ i ∈ F, A i) B = ⋃ i ∈ F, setMul (A i) B := by
  ext g
  simp only [setMul, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, hi, hx⟩, y, hy, rfl⟩
    exact ⟨i, hi, x, hx, y, hy, rfl⟩
  · rintro ⟨i, hi, x, hx, y, hy, rfl⟩
    exact ⟨x, ⟨i, hi, hx⟩, y, hy, rfl⟩

/-- The cell of a product is contained in the product of cells: $C(ww') \subseteq C(w) \cdot C(w')$. -/
theorem bruhatCell_sub_setMul (bp : BNPair G M) (w w' : M.Group) :
    bp.bruhatCell (w * w') ⊆ setMul (bp.bruhatCell w) (bp.bruhatCell w') := by
  intro g hg
  obtain ⟨⟨b₁, hb₁⟩, n, ⟨b₂, hb₂⟩, hπ, hg_eq⟩ := hg
  obtain ⟨n_w, hn_w⟩ := bp.π_surj w
  obtain ⟨n_w', hn_w'⟩ := bp.π_surj w'
  have hπ_prod : bp.π (n_w * n_w') = w * w' := by rw [map_mul, hn_w, hn_w']

  have hπ_diff : bp.π ((n_w * n_w')⁻¹ * n) = 1 := by
    rw [map_mul, map_inv, hπ_prod, hπ, inv_mul_cancel]
  have diff_in_T : (((n_w * n_w')⁻¹ * n : bp.N) : G) ∈ bp.T :=
    (bp.π_ker _).mp hπ_diff
  have diff_in_B : (((n_w * n_w')⁻¹ * n : bp.N) : G) ∈ bp.B := by
    rw [bp.T_eq] at diff_in_T; exact (Subgroup.mem_inf.mp diff_in_T).1

  refine ⟨(b₁ : G) * (n_w : G), ?_,
    (n_w' : G) * (((n_w * n_w')⁻¹ * n : bp.N) : G) * (b₂ : G), ?_, ?_⟩
  ·
    exact ⟨⟨b₁, hb₁⟩, n_w, ⟨1, bp.B.one_mem⟩, hn_w, by simp⟩
  ·
    exact ⟨⟨1, bp.B.one_mem⟩, n_w',
      ⟨((n_w * n_w')⁻¹ * n : bp.N) * b₂, bp.B.mul_mem diff_in_B hb₂⟩,
      hn_w', by simp [Subgroup.coe_mul]; group⟩
  ·
    rw [hg_eq]
    have : (n : G) = (n_w : G) * (n_w' : G) * (((n_w * n_w')⁻¹ * n : bp.N) : G) := by
      simp [Subgroup.coe_mul]; group
    rw [this]; group

end CellMulFinite
