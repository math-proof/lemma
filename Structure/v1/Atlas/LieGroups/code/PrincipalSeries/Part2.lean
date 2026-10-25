/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.IsInQPlus0
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Abbrev.v1.Atlas.LieGroups.code.PrincipalSeries


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

structure PrincipalSeriesBimodule
    (Δ : TriangularDecomposition R 𝔤) where
  wt_lambda : Δ.𝔥 →ₗ[R] R
  wt_mu : Δ.𝔥 →ₗ[R] R
  M_source : Type u_mod
  [M_source_acg : AddCommGroup M_source]
  [M_source_mod : Module R M_source]
  [M_source_lrm : LieRingModule 𝔤 M_source]
  [M_source_lm : LieModule R 𝔤 M_source]
  verma_source : IsVermaModule Δ M_source wt_lambda
  M_target : Type u_mod
  [M_target_acg : AddCommGroup M_target]
  [M_target_mod : Module R M_target]
  [M_target_lrm : LieRingModule 𝔤 M_target]
  [M_target_lm : LieModule R 𝔤 M_target]
  verma_target : IsVermaModule Δ M_target wt_mu

end
