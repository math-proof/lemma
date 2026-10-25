/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOverTensorProductSurjective.lean -/

import Def.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProduct
import Lemma.Nat.NumberField.Completion.FinitePlacesOverTensorProduct
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Topology.Algebra.Module.FiniteDimension
/-!
# Surjectivity of the finite-place completion tensor product map

For a number field extension `L / K` and a finite place `v` of `K`, the canonical
`v.adicCompletion K`-algebra map `completionTensorProductMap v` into the product of the
`w`-adic completions over all places `w` of `L` above `v` is surjective.

The proof is by weak approximation for the pairwise inequivalent finite-place absolute
values, transported to the completions along isometric coordinate maps, so the diagonal
map out of `L` is dense; precomposing with `y ↦ 1 ⊗ₜ y` makes the tensor product map
dense, and its range is finite-dimensional over `v.adicCompletion K`, hence closed.

## ATLAS source correspondence

This is the surjectivity clause of ATLAS NumberTheoryI N265, Theorem 13.5.
At atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the theorem is indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879),
and the finite-place map is
[`GlobalFields.canonicalMap_finite`, lines 726--738](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L726-L738).
Its source surjectivity result is
[`canonicalMap_finite_surjective_by_approx`, lines 983--1023](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L983-L1023)
(and the later wrapper at
[lines 1088--1138](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1088-L1138)).
The map is the same one
constructed as `completionTensorProductMap` in the preceding stage, up to the
documented canonical swap from `L ⊗[K] K_v` to `K_v ⊗[K] L`, with the same
dependent product over `w ∣ v` and the same chosen completion maps.

The source proof obtains surjectivity from a finite-dimensional dimension
equality plus injectivity; that injectivity passes through the admission-backed
[`canonicalMap_finite_ker_eq_bot` at lines 978--981](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L978-L981).
This module replaces only
that proof route, not the statement:

* `denseRange_algebraMap_placesOver` applies weak approximation to the
  pairwise inequivalent normalized `w`-adic absolute values and transports the
  dense diagonal image of `L` into `∏_{w ∣ v} L_w` through isometric completion
  maps;
* `denseRange_completionTensorProductMap` factors that diagonal map through
  `y ↦ 1 ⊗ₜ y`, proving the source canonical tensor map has dense range; and
* `completionTensorProductMap_surjective` observes that its linear range is
  finite-dimensional over `K_v`, hence closed. A dense closed subspace is the
  whole target, yielding exactly the source surjectivity conclusion.

This proves no injectivity or equivalence claim; those remain separate stages
of N265.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField Valued

open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

open scoped NumberField.LiesOver

open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K))

noncomputable def coord (w : v.placesOver L) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val) →+*
      w.val.adicCompletion L :=
  (NumberField.FinitePlace.embedding w.val).comp (WithAbs.equiv _).toRingHom

end IsDedekindDomain.HeightOneSpectrum
