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

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v

namespace Corollary1278

/-- For a finite `k`-algebra `H` over an algebraically closed field `k`, the structure map
`k → H/𝔪` to any residue field at a maximal ideal is an algebra isomorphism. -/
noncomputable def residueFieldEquivOfAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type v) [CommRing H] [Algebra k H] [Module.Finite k H]
    (I : MaximalSpectrum H) : k ≃ₐ[k] (H ⧸ I.asIdeal) := by
  haveI : IsDomain (H ⧸ I.asIdeal) := Ideal.Quotient.isDomain I.asIdeal
  haveI : Module.Finite k (H ⧸ I.asIdeal) :=
    Module.Finite.quotient k (I.asIdeal.restrictScalars k)
  haveI : Algebra.IsIntegral k (H ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ I.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- For a finite-dimensional commutative Hopf algebra `H` over `k`, the maximal spectrum
of `H` inherits a group structure (dual to the comultiplication on `H`). -/
end Corollary1278

section FunAlgEquivEquiv

variable {k : Type u} [Field k] {G₁ : Type v} [Fintype G₁] [DecidableEq G₁]
  {G₂ : Type v} [Fintype G₂] [DecidableEq G₂]

/-- A `k`-algebra equivalence `(G₁ → k) ≃ₐ[k] (G₂ → k)` between finite product algebras
of copies of `k` induces a map `G₂ → G₁` by identifying evaluation algebra homomorphisms
on the codomain with those on the domain. -/
noncomputable def funAlgEquivInducedMap (e : (G₁ → k) ≃ₐ[k] (G₂ → k)) : G₂ → G₁ := fun g₂ =>
  (AlgHom.eq_piEvalAlgHom ((Pi.evalAlgHom k (fun _ : G₂ => k) g₂).comp e.toAlgHom)).choose

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

namespace Corollary1278

/-- For Hopf algebra equivalences `e₁ : H ≃ₐ (G₁ → k)` and `e₂ : H ≃ₐ (G₂ → k)`, the
induced point map `G₂ → G₁` from `e₁.symm.trans e₂` is a group homomorphism. -/
end Corollary1278

set_option maxHeartbeats 800000 in
/-- Corollary 1.27.8 (existence): every finite-dimensional commutative Hopf algebra over
an algebraically closed field of characteristic zero is isomorphic to the algebra of
functions `Fun(G, k)` on a finite group `G`. -/
namespace Corollary1278

/-- For a finite-dimensional commutative Hopf algebra `H ≅ Fun(G, k)`, the preimage of
each indicator function `δ_g` is a grouplike element of `H`. -/
end Corollary1278
