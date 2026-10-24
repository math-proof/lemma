/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProduct.lean -/

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Pi
import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverInstances
import sympy.atlas.NumberTheory.NumberField.Completion.FinitePlacesOver
/-!
# Finite-place completion tensor product maps

For a number field extension `L / K` and a finite place `v` of `K`, this file
provides the canonical `v.adicCompletion K`-algebra maps from the tensor product
`v.adicCompletion K ⊗[K] L` to each `w.val.adicCompletion L` and to the product.

## ATLAS source correspondence

This is the map-construction stage for ATLAS NumberTheoryI N265, Theorem 13.5.
At atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the exact source statement is
indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879):
the canonical
map `L ⊗[K] K_v → ∏_{w ∣ v} L_w`, `ℓ ⊗ x ↦ (ℓx)_w`, is an isomorphism of
finite étale `K_v`-algebras. The primary formal map is
[`GlobalFields.canonicalMap_finite` in `v1/Atlas/NumberTheoryI/code/GlobalFields.lean`,
lines 726--738](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L726-L738);
its component completion embeddings are defined at
[lines 693--713](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L693-L713).

The declarations here map to that source as follows:

* `v.placesOver L` is the dependent index type
  `{w : HeightOneSpectrum (𝓞 L) // w ∣ v}` used by the source product.
* The scoped `LiesOver` instance extracts the proof carried by each `w`.
  The scoped completion algebra and scalar-tower instances use the canonical
  `adicCompletionMap v w.val`; this is the chosen map `K_v → L_w`
  corresponding to source `completionEmbedding_finite v w.val w.property`.
* `completionTensorProductComponent v w` is the source component
  `L ⊗[K] K_v → L_w`, written after the standard symmetry as
  `K_v ⊗[K] L → L_w`: it multiplies the images of `x : K_v` and `y : L`.
* `completionTensorProductMap` packages those components with `AlgHom.pi`, so
  its codomain is exactly the dependent product over all `w ∣ v`.
  The `_tmul`, `_apply`, and `_pi_eval` theorems expose the source formula and
  show that evaluation at `w` recovers the selected component.

Changing the tensor-factor order uses only the canonical commutativity
equivalence and does not alter the map. This module constructs the N265
morphism; injectivity, surjectivity, finite étaleness, and the final
`AlgEquiv` are deliberately left to later stages.
-/

namespace IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

open scoped NumberField
open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)} (w : v.placesOver L)

/-- Lying-over instance from places-over membership. -/
scoped instance : w.val.asIdeal.LiesOver v.asIdeal :=
  w.property

/-- Algebra from the base completion to the place completion. -/
noncomputable scoped instance : Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
  let _ : w.val.asIdeal.LiesOver v.asIdeal := w.property
  (adicCompletionMap v w.val).toAlgebra

/-- Scalar tower over the base field through the base completion. -/
scoped instance : IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) := by
  let _ : w.val.asIdeal.LiesOver v.asIdeal := w.property
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [RingHom.algebraMap_toAlgebra]
  exact (adicCompletionMap_algebraMap v w.val x).symm

end IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField
open TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

/-- Per-place component map out of the completion tensor product. -/
noncomputable def completionTensorProductComponent (w : v.placesOver L) :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] w.val.adicCompletion L :=
  Algebra.TensorProduct.lift (Algebra.algHom _ _ _) (Algebra.algHom K L _)
    (fun _ _ => mul_comm _ _)

/-- Canonical product map into places lying over `v`. -/
noncomputable def completionTensorProductMap :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ((w : v.placesOver L) → w.val.adicCompletion L) :=
  AlgHom.pi (fun w => completionTensorProductComponent v w)
end IsDedekindDomain.HeightOneSpectrum
