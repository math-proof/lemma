/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.GKModule
import sympy.atlas.v1.Atlas.LieGroups.code.SL2Basics
import Lemma.Nat.basisHC.eq.SMul
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Lie.OfAssociative

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only
attribute [local instance 100] LieRing.ofAssociativeRing

open Module

noncomputable section

structure SL2GKModule
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    extends GKModule 𝔤 K 𝔨 Ad V where
  H : 𝔤
  E : 𝔤
  F : 𝔤
  bracket_HE : ⁅H, E⁆ = (2 : ℤ) • E
  bracket_HF : ⁅H, F⁆ = (-2 : ℤ) • F
  bracket_EF : ⁅E, F⁆ = H
  sl2_span : ∀ X : 𝔤, ∃ a b c : ℂ, X = a • H + b • E + c • F
  K_centralizes : ∀ k : K, Ad k H = H

namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {K : Type*} [Group K]
variable {𝔨 : LieSubalgebra ℂ 𝔤}
variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

def hEnd (M : SL2GKModule 𝔤 K 𝔨 Ad V) : Module.End ℂ V :=
  (LieModule.toEnd ℂ 𝔤 V) M.H

def weightSpace (M : SL2GKModule 𝔤 K 𝔨 Ad V) (n : ℤ) : Submodule ℂ V :=
  Module.End.eigenspace M.hEnd (n : ℂ)

def iterLie (X : 𝔤) (v : V) : ℕ → V
  | 0 => v
  | k + 1 => ⁅X, iterLie X v k⁆

omit [LieAlgebra ℂ 𝔤] [Module ℂ V] [LieModule ℂ 𝔤 V] in
@[simp] theorem iterLie_zero (X : 𝔤) (v : V) : iterLie X v 0 = v := rfl
omit [LieAlgebra ℂ 𝔤] [Module ℂ V] [LieModule ℂ 𝔤 V] in
@[simp] theorem iterLie_succ (X : 𝔤) (v : V) (k : ℕ) :
    iterLie X v (k + 1) = ⁅X, iterLie X v k⁆ := rfl

def ktypeSet (M : SL2GKModule 𝔤 K 𝔨 Ad V) : Set ℤ :=
  {n : ℤ | M.weightSpace n ≠ ⊥}

theorem sl2_linearIndependent : LinearIndependent ℂ ![sl2H, sl2E, sl2F] := by
  apply LinearIndependent.of_comp sl2C.toSubmodule.subtype
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three] at hg
  have h00 := congr_fun (congr_fun hg 0) 0
  have h01 := congr_fun (congr_fun hg 0) 1
  have h10 := congr_fun (congr_fun hg 1) 0
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             sl2H, sl2E, sl2F, basisH_C, basisE_C, basisF_C,
             Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply,
             smul_eq_mul, Submodule.subtype_apply] at h00 h01 h10
  intro i
  fin_cases i <;> simp_all

def sl2Basis : Module.Basis (Fin 3) ℂ ↥sl2C :=
  basisOfLinearIndependentOfCardEqFinrank sl2_linearIndependent
    (by simp [Fintype.card_fin, finrank_sl2C])

end SL2GKModule
