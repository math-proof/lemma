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

end FunAlgEquivEquiv
