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
import Def.v1.Atlas.TensorCategories.code.CartierKostant.CommHopfFunGroup
open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section FunAlgEquivEquiv

variable {k : Type u} [Field k] {G₁ : Type v} [Fintype G₁] [DecidableEq G₁]
  {G₂ : Type v} [Fintype G₂] [DecidableEq G₂]

omit [DecidableEq G₁] [Fintype G₂] [DecidableEq G₂] in
/-- Defining property of `funAlgEquivInducedMap`: evaluation of `f` at the induced point
`funAlgEquivInducedMap e g₂` agrees with evaluation of `e f` at `g₂`. -/
lemma funAlgEquivInducedMap_spec (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) (g₂ : G₂) (f : G₁ → k) :
    f (funAlgEquivInducedMap e g₂) = (e f) g₂ := by
  have := (AlgHom.eq_piEvalAlgHom
    ((Pi.evalAlgHom k (fun _ : G₂ => k) g₂).comp e.toAlgHom)).choose_spec
  have h := congr_fun (congr_arg DFunLike.coe this) f
  simp only [Pi.evalAlgHom_apply, AlgHom.comp_apply] at h
  exact h.symm

omit [DecidableEq G₁] [Fintype G₂] in
/-- The induced map `funAlgEquivInducedMap e : G₂ → G₁` from an algebra equivalence is
injective. -/
lemma funAlgEquivInducedMap_injective (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) :
    Function.Injective (funAlgEquivInducedMap e) := by
  intro g₂ g₂' heq
  by_contra hne
  have key : ∀ f : G₂ → k, f g₂ = f g₂' := by
    intro f
    have h1 := funAlgEquivInducedMap_spec e g₂ (e.symm f)
    have h2 := funAlgEquivInducedMap_spec e g₂' (e.symm f)
    simp only [AlgEquiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, heq]
  have := key (Pi.single g₂ 1)
  simp [hne] at this

end FunAlgEquivEquiv
