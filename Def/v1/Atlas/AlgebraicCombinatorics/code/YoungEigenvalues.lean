/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungEigenvalues.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungTableaux
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungTableaux
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
set_option autoImplicit false


noncomputable section

namespace YoungEigenvalues

noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def kerDimDiff (s : ℕ) : ℕ :=
  if s = 0 then p 0 else p s - p (s - 1)

noncomputable def adjOp₂ {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁]
    [AddCommGroup V₂] [Module ℝ V₂] (U : V₁ →ₗ[ℝ] V₂) (D : V₂ →ₗ[ℝ] V₁) :
    Module.End ℝ (V₁ × V₂) where
  toFun p := (D p.2, U p.1)
  map_add' p q := by simp [map_add]
  map_smul' r p := by simp [map_smul]

noncomputable def eigenspace_adjOp₂_equiv_DU
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
    [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
    (U : V₁ →ₗ[ℝ] V₂) (D : V₂ →ₗ[ℝ] V₁)
    (μ : ℝ) (hμ : μ ≠ 0) (s : ℝ) (hμs : μ * μ = s) :
    (adjOp₂ U D).eigenspace μ ≃ₗ[ℝ] Module.End.eigenspace (D.comp U) s :=
  LinearEquiv.ofLinear
    { toFun := fun ⟨⟨a, b⟩, hab⟩ => ⟨a, by
        rw [Module.End.mem_eigenspace_iff, LinearMap.comp_apply]
        have h := Module.End.mem_eigenspace_iff.mp hab
        have hDb : D b = μ • a := congr_arg Prod.fst h
        have hUa : U a = μ • b := congr_arg Prod.snd h
        rw [hUa, map_smul, hDb, smul_smul, hμs]⟩
      map_add' := fun _ _ => Subtype.ext rfl
      map_smul' := fun _ _ => Subtype.ext rfl }
    { toFun := fun ⟨a, ha⟩ => ⟨(a, μ⁻¹ • U a), by
        rw [Module.End.mem_eigenspace_iff]
        have hDUa : D (U a) = s • a := Module.End.mem_eigenspace_iff.mp ha
        show adjOp₂ U D (a, μ⁻¹ • U a) = μ • (a, μ⁻¹ • U a)
        simp only [adjOp₂, LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_mk]
        ext
        · simp only [LinearMap.map_smul, hDUa, smul_smul]
          congr 1; rw [← hμs]; field_simp
        · simp only [smul_smul, mul_inv_cancel₀ hμ, one_smul]⟩
      map_add' := fun ⟨a₁, _⟩ ⟨a₂, _⟩ => by
        apply Subtype.ext; simp [smul_add, map_add]
      map_smul' := fun r ⟨a, _⟩ => by
        apply Subtype.ext; simp [smul_comm r, map_smul] }
    (by ext1 ⟨a, ha⟩; exact Subtype.ext rfl)
    (by ext1 ⟨⟨a, b⟩, hab⟩; apply Subtype.ext
        have hUa : U a = μ • b := congr_arg Prod.snd (Module.End.mem_eigenspace_iff.mp hab)
        show (a, μ⁻¹ • U a) = (a, b)
        rw [hUa, smul_smul, inv_mul_cancel₀ hμ, one_smul])

noncomputable def eigenspace_comp_comm_nonzero_equiv
    {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂]
    (A : W₁ →ₗ[ℝ] W₂) (B : W₂ →ₗ[ℝ] W₁) (μ : ℝ) (hμ : μ ≠ 0) :
    Module.End.eigenspace (B.comp A) μ ≃ₗ[ℝ]
      Module.End.eigenspace (A.comp B) μ :=
  LinearEquiv.ofLinear
    { toFun := fun ⟨w, hw⟩ => ⟨A w, by
        rw [Module.End.mem_eigenspace_iff]
        have hBAw : B (A w) = μ • w := by
          rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hw
        show (A.comp B) (A w) = μ • A w
        rw [LinearMap.comp_apply, hBAw, map_smul]⟩
      map_add' := fun _ _ => Subtype.ext (map_add A _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul A _ _) }
    { toFun := fun ⟨v, hv⟩ => ⟨μ⁻¹ • B v, by
        rw [Module.End.mem_eigenspace_iff]
        have hABv : A (B v) = μ • v := by
          rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hv
        show (B.comp A) (μ⁻¹ • B v) = μ • (μ⁻¹ • B v)
        rw [LinearMap.comp_apply, map_smul, map_smul, hABv, map_smul,
            smul_smul, smul_smul, inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ]⟩
      map_add' := fun ⟨a₁, _⟩ ⟨a₂, _⟩ => by
        apply Subtype.ext; show μ⁻¹ • B (a₁ + a₂) = μ⁻¹ • B a₁ + μ⁻¹ • B a₂
        rw [map_add, smul_add]
      map_smul' := fun r ⟨a, _⟩ => by
        apply Subtype.ext; show μ⁻¹ • B (r • a) = r • (μ⁻¹ • B a)
        rw [map_smul, smul_comm] }
    (by
      ext1 ⟨v, hv⟩; apply Subtype.ext
      show A (μ⁻¹ • B v) = v
      have hABv : A (B v) = μ • v := by
        rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hv
      rw [map_smul, hABv, smul_smul, inv_mul_cancel₀ hμ, one_smul])
    (by
      ext1 ⟨w, hw⟩; apply Subtype.ext
      show μ⁻¹ • B (A w) = w
      have hBAw : B (A w) = μ • w := by
        rw [← LinearMap.comp_apply]; exact Module.End.mem_eigenspace_iff.mp hw
      rw [hBAw, smul_smul, inv_mul_cancel₀ hμ, one_smul])

end YoungEigenvalues
end
