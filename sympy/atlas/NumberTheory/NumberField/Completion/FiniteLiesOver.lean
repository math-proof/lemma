/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOver.lean -/

import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Canonical maps between finite-place completions

For a number-field extension `L / K` and finite places `v` of `K` and `w`
of `L` with `w` lying over `v`, this file constructs the canonical
map `adicCompletionMap` between the finite-place completions, with its
algebra-map formula (`adicCompletionMap_algebraMap`), continuity, and
injectivity.

This is only the finite-place completion-map prerequisite for the full
N265 theorem (ATLAS NumberTheoryI N265, Theorem 13.5, Section 13.1), not
the tensor-product equivalence itself. At ATLAS revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the final source theorem is
[`theorem_13_5_finite_place_Kv`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1166),
with the underlying ring/algebra equivalence
[`theorem_13_5_finite_place`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1143-L1150).

Source map from the ATLAS sources to this file's API:

The direct source constructions are
[`AdicCompletionAlgebra.adicCompletionMap` and `adicCompletionMap_comp_algebraMap`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean#L186-L220).
The parallel N265-specific construction consists of
[`completionEmbedding_finite_ringHom`, `completionEmbedding_finite_continuous`,
and `completionEmbedding_finite`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L534-L713).

Source conventions used here:

* Finite places are `HeightOneSpectrum (𝓞 K)` and `HeightOneSpectrum (𝓞 L)`,
  exactly the current `v` and `w`.
* Source [`FinitePlace.LiesAbove w v`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L75-L78)
  is defined by `w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal`.
  The current instance `[w.asIdeal.LiesOver v.asIdeal]` is Mathlib's bundled
  version of the same equality (with its field stored in the opposite
  equality orientation).
* `v.valuation K` and `w.valuation L` are the canonical height-one adic
  valuations used on the base and extension fields.
* `WithVal (v.valuation K)` and `WithVal (w.valuation L)` are the fields
  equipped with those valuations; `UniformSpace.Completion.mapRingHom`
  extends their algebra map continuously using Mathlib's
  `uniformContinuous_algebraMap_liesOver K L v w`.
* `adicCompletion.equiv K v` and `adicCompletion.equiv L w` are the ring
  equivalences identifying Mathlib's `adicCompletion` wrappers with those
  uniform completions. The definition transports to the source completion,
  applies the completed algebra map, and transports back.
* `adicCompletionMap_algebraMap` is the source compatibility formula;
  continuity is inherited from the two equivalences and
  `Completion.continuous_map`; injectivity follows because the resulting
  ring homomorphism is between fields.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [hvw : w.asIdeal.LiesOver v.asIdeal]

noncomputable def adicCompletionMap :
    v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver K L v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom)

@[simp]
theorem adicCompletionMap_algebraMap (x : K) :
    adicCompletionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x := by
  apply adicCompletion.ext
  change UniformSpace.Completion.map
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (↑(algebraMap K (WithVal (v.valuation K)) x)) =
    ↑(algebraMap K (WithVal (w.valuation L)) x)
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_algebraMap_liesOver K L v w)]
  rfl

include hvw in
theorem continuous_adicCompletionMap :
    Continuous (adicCompletionMap v w) := by
  unfold adicCompletionMap
  exact ((adicCompletion.continuous_ofCompletion L w).comp
    UniformSpace.Completion.continuous_map).comp
    (adicCompletion.continuous_toCompletion K v)

include hvw in
theorem adicCompletionMap_injective :
    Function.Injective (adicCompletionMap v w) :=
  RingHom.injective _

end IsDedekindDomain.HeightOneSpectrum
