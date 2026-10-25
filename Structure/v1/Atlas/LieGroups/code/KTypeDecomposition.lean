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
attribute [local instance 100] LieRing.ofAssociativeRing

open Module

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


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

end
