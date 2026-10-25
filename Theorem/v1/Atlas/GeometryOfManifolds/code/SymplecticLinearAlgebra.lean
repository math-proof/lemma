/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
open Module


namespace SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An alternating bilinear form is skew-symmetric: $\Omega(x, y) = -\Omega(y, x)$. -/
theorem sympl_skew {Ω : LinearMap.BilinForm ℝ V} (hAlt : Ω.IsAlt) (x y : V) :
    Ω x y = -(Ω y x) := by
  have h := hAlt (x + y)
  simp [map_add, LinearMap.add_apply] at h
  linarith [hAlt x, hAlt y]

/-- Dimension formula for the symplectic orthogonal: $\dim E + \dim E^\Omega = \dim V$. -/
lemma symplecticOrtho_finrank_add [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (E : Submodule ℝ V) :
    finrank ℝ ↥E + finrank ℝ ↥(symplecticOrtho Ω E) = finrank ℝ V := by
  have hRefl : Ω.IsRefl := hΩ.alt.isRefl
  have key := LinearMap.BilinForm.finrank_add_finrank_orthogonal hRefl E
  have htop : Ω.orthogonal ⊤ = ⊥ := hΩ.orthogonal_top_eq_bot
  rw [htop] at key
  have hbot : finrank ℝ ↥(E ⊓ ⊥) = 0 := by rw [inf_bot_eq]; exact finrank_bot ℝ V
  unfold symplecticOrtho
  linarith

/-- $E$ is a symplectic subspace iff $E$ and $E^\Omega$ are complementary: $V = E \oplus E^\Omega$. -/
theorem symplectic_subspace_iff [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (E : Submodule ℝ V) :
    IsSymplecticSubspace Ω E ↔ IsCompl E (symplecticOrtho Ω E) := by
  unfold IsSymplecticSubspace
  constructor
  · intro hE
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]; exact hE
    · rw [codisjoint_iff]
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq E (symplecticOrtho Ω E)
      rw [hE] at hsup
      simp at hsup
      have hadd := symplecticOrtho_finrank_add hΩ E
      exact Submodule.eq_top_of_finrank_eq (by linarith)
  · intro ⟨hd, _⟩
    exact hd.eq_bot

/-- A Lagrangian subspace has half the dimension of the ambient symplectic space:
$2 \dim E = \dim V$. -/
theorem lagrangian_half_dim [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    2 * finrank ℝ ↥E = finrank ℝ V := by
  unfold IsLagrangian symplecticOrtho at hE
  have hadd := symplecticOrtho_finrank_add hΩ E
  unfold symplecticOrtho at hadd
  rw [hE] at hadd
  omega

end SymplecticLinearAlgebra
