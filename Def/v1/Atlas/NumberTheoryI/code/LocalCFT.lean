/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.NumberTheoryI.code.LocalCFT
open scoped RestrictedProduct
open Filter Set


noncomputable section

open scoped Pointwise

section MaximalExtensions

variable (K Ksep : Type*) [Field K] [Field Ksep] [Algebra K Ksep]

def IsFiniteAbelianExtension (L : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K L ∧ IsGalois K L ∧
    ∀ (σ τ : L ≃ₐ[K] L), σ * τ = τ * σ

def IsFiniteUnramifiedExtension (L : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K L ∧ Algebra.FormallyUnramified K L

def maximalAbelianExtension : IntermediateField K Ksep :=
  ⨆ (L : IntermediateField K Ksep) (_ : IsFiniteAbelianExtension K Ksep L), L

end MaximalExtensions
end
