/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Lie.OfAssociative
import Def.v1.Atlas.LieGroups.code.KTypeDecomposition.Part2
attribute [local instance 100] LieRing.ofAssociativeRing

open Module

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

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

end SL2GKModule
end
