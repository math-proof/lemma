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
import Structure.v1.Atlas.LieGroups.code.PrincipalSeries.Part3


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] PrincipalSeriesBimodule.M_source_acg
  PrincipalSeriesBimodule.M_source_mod PrincipalSeriesBimodule.M_source_lrm
  PrincipalSeriesBimodule.M_source_lm PrincipalSeriesBimodule.M_target_acg
  PrincipalSeriesBimodule.M_target_mod PrincipalSeriesBimodule.M_target_lrm
  PrincipalSeriesBimodule.M_target_lm

def BorelBimoduleHom
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    {X : Type*} [AddCommGroup X] [Module R X]
    (hX : PS_IsHarishChandraBimodule R 𝔤 X) : Type _ :=
  { φ : X →ₗ[R] R //
    (∀ (f : Δ.𝔫_neg) (x : X), φ (hX.left_action f x) = 0) ∧
    (∀ (e : Δ.𝔫_pos) (x : X), φ (hX.right_action e x) = 0) ∧
    (∀ (h : Δ.𝔥) (x : X), φ (hX.left_action h x) = P.wt_mu h * φ x) ∧
    (∀ (h : Δ.𝔥) (x : X), φ (hX.right_action h x) = P.wt_lambda h * φ x) }

def IntermediateBorelHom
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (P : PrincipalSeriesBimodule Δ)
    {X : Type*} [AddCommGroup X] [Module R X]
    (hX : PS_IsHarishChandraBimodule R 𝔤 X) : Type _ :=
  { φ : X →ₗ[R] R //

    (∀ (e : Δ.𝔫_pos) (x : X), φ (hX.right_action e x) = 0) ∧

    (∀ (h : Δ.𝔥) (x : X), φ (hX.right_action h x) = P.wt_lambda h * φ x) }

end
