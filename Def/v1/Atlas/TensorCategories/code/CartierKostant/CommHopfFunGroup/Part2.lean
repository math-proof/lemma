/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/CommHopfFunGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Category.Atlas.v1.TensorCategories.code.CartierKostant.Theorems
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Theorem.v1.Atlas.TensorCategories.code.CartierKostant.CommHopfFunGroup
open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section FunAlgEquivEquiv

variable {k : Type u} [Field k] {G₁ : Type v} [Fintype G₁] [DecidableEq G₁]
  {G₂ : Type v} [Fintype G₂] [DecidableEq G₂]

/-- Upgrade `funAlgEquivInducedMap` to a bijection `G₂ ≃ G₁` using injectivity of both
sides and finite cardinalities. -/
noncomputable def funAlgEquivInducedEquiv (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) : G₂ ≃ G₁ := by
  apply Equiv.ofBijective (funAlgEquivInducedMap e)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨funAlgEquivInducedMap_injective e, ?_⟩
  have h1 := Fintype.card_le_of_injective _ (funAlgEquivInducedMap_injective e)
  have h2 := Fintype.card_le_of_injective _ (funAlgEquivInducedMap_injective e.symm)
  omega

end FunAlgEquivEquiv
