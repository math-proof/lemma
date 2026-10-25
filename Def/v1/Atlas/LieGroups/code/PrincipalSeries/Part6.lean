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
import Structure.v1.Atlas.LieGroups.code.PrincipalSeries.Part6


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

attribute [instance] SmoothSectionsFinite.carrier_acg SmoothSectionsFinite.carrier_mod

attribute [instance] FunctorHLambda.M_lambda_acg FunctorHLambda.M_lambda_mod
  FunctorHLambda.M_lambda_lrm FunctorHLambda.M_lambda_lm

def FunctorHLambda.onObject
    {Δ : TriangularDecomposition R 𝔤}
    {wt_lambda : Δ.𝔥 →ₗ[R] R}
    (H : FunctorHLambda Δ wt_lambda)
    (X : Type u_mod) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X] : Type _ :=
  { f : H.M_lambda →ₗ⁅R, 𝔤⁆ X // IsLocallyFiniteMap R (f : H.M_lambda →ₗ[R] X) }

def FunctorHLambda.onMorphism
    {Δ : TriangularDecomposition R 𝔤}
    {wt_lambda : Δ.𝔥 →ₗ[R] R}
    (H : FunctorHLambda Δ wt_lambda)
    {X Y : Type u_mod} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (φ : X →ₗ⁅R, 𝔤⁆ Y)
    (hx : H.onObject X) : H.onObject Y :=
  ⟨φ.comp hx.val,


   by
    have hfg : (LinearMap.range (hx.val : H.M_lambda →ₗ[R] X)).FG := hx.property
    change (LinearMap.range (LieModuleHom.toLinearMap (φ.comp hx.val))).FG
    rw [LieModuleHom.toLinearMap_comp, LinearMap.range_comp]
    exact hfg.map _⟩

set_option linter.unusedVariables false in

def IsDominantWeight
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, ∃ (n : ℕ), rd.corootPairing wt α = (n : R)

end
