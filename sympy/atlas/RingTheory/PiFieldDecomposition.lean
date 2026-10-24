/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldDecomposition.lean -/

-- MathlibExt/RingTheory/PiFieldDecomposition.lean

import sympy.atlas.RingTheory.PiFieldQuotient
import Lemma.Int.PiFieldQuotient
/-!
# Uniqueness of finite products of fields up to permutation

Let `K` be a field and `F : ι → Type*`, `G : κ → Type*` finite families of fields
with `K`-algebra structures. Any `K`-algebra equivalence between the products
`(∀ i, F i)` and `(∀ j, G j)` induces a permutation of the index types, unique up
to the evident relabelling, together with factorwise `K`-algebra equivalences:
there is `σ : ι ≃ κ` such that `F i ≃ₐ[K] G (σ i)` for every `i`.

The proof goes through one field at a time: a surjective algebra map from a
finite product of fields to a field factors through exactly one coordinate
(`PiFieldQuotient.exists_algEquiv_restrict` plus a singleton-support argument),
and applying this to each coordinate in both directions yields inverse index
maps whose composites are the identity.

This is the corrected form of ATLAS `NumberTheoryI` target N83, Corollary 4.33.
At atlas-lean revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
the [English target is lines 521--525 of `v1/Atlas/NumberTheoryI/targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L521-L525),
and the primary Lean source is
[`EtaleAlgebra.etale_decomposition_unique` in
`v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean`, lines 180--188](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean#L180-L188).
Given an equivalence between
`∏ i, F i` and `∏ j, G j`, that theorem concludes only mutual coverage:
every `F i` is equivalent to some `G j`, and every `G j` to some `F i`.
Those two choices need not be inverse and therefore do not retain factor
multiplicities; for example, families of one and two identical rational factors
satisfy that conclusion even though their index types are not equivalent.

Corollary 4.33 says uniqueness *up to permutation and isomorphism of factors*.
Accordingly, `exists_indexEquiv_algEquiv` retains the same product-algebra
equivalence hypothesis but strengthens the source conclusion to one equivalence
`σ : ι ≃ κ` together with aligned factor equivalences
`F i ≃ₐ[K] G (σ i)`. This records multiplicity and supplies the alignment needed
by downstream N266. The `[Finite]` hypotheses merely avoid exposing choices of
enumeration or decidable equality; the proof makes those choices internally.
-/

universe u v w x y

namespace PiFieldQuotient

/-- The product over a singleton index type is algebra-equivalent to its only factor. -/
private noncomputable def singletonEquiv {K : Type*} [Field K] {ι : Type*}
    {F : ι → Type*} [∀ i, Semiring (F i)] [∀ i, Algebra K (F i)]
    (S : Finset ι) (s0 : S) (hsing : ∀ s : S, s = s0) :
    (∀ s : S, F (s : ι)) ≃ₐ[K] F ((s0 : S) : ι) :=
  { toFun := fun f => f s0
    invFun := fun x s => hsing s ▸ x
    left_inv := fun f => by ext s; rw [hsing s]
    right_inv := fun x => by rfl
    map_mul' := fun _ _ => by rfl
    map_add' := fun _ _ => by rfl
    commutes' := fun _ => by rfl }
end PiFieldQuotient
