/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverValuation.lean -/

import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOver
import Lemma.Nat.NumberField.Completion.FiniteLiesOver
import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverValuation
/-!
# Valuation formula for maps between finite-place completions

## ATLAS source-to-API map

This file is only a supporting/prerequisite stage for ATLAS NumberTheoryI item
N265; it does not prove the full tensor-product equivalence. The N265 target is
the source module `Atlas.NumberTheoryI.GlobalFields` at ATLAS revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, final declaration
[`theorem_13_5_finite_place_Kv`, lines 1152--1211](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1211).

Source-to-API correspondences used here:

* Source completion map
  [`completionEmbedding_finite`, lines 693--713](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L693-L713)
  is the imported `adicCompletionMap` used here. Its construction uses
  [`completionEmbedding_finite_ringHom`, lines 534--539](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L534-L539),
  and the continuity work ending at
  [`completionEmbedding_finite_continuous`, lines 668--672](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L668-L672).
* The second exact source is
  [`CompleteFields.valuation_extends_with_ramificationIdx`, lines 275--301](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/CompleteFields.lean#L275-L301).
  Its
  source exponent `Ideal.ramificationIdx` is Mathlib's
  `Ideal.ramificationIdx'` here (written `v.asIdeal.ramificationIdx' w.asIdeal`).
* Source [`FinitePlace.LiesAbove w v`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L75-L78) corresponds to
  `[w.asIdeal.LiesOver v.asIdeal]` here (stored as a comap equality).
* `[NumberField K] [NumberField L] [Algebra K L]` plus the lies-over instance
  correspond to the source number-field extension `L/K` and finite place `w`
  above `v`.

Local API roles: `valuation_adicCompletionMap` extends the source valuation
identity from the dense embedded copy of `K` to all of `v.adicCompletion K` by
continuity; `adicCompletionMap_mem_integers` translates it to the
valuation-subring condition; and `adicCompletionIntegersMap` restricts the same
map to the integer rings.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

open WithZeroTopology

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Canonical restricted map between adic integer rings. -/
noncomputable def adicCompletionIntegersMap :
    v.adicCompletionIntegers K →+* w.adicCompletionIntegers L where
  toFun x := ⟨adicCompletionMap v w x.val, adicCompletionMap_mem_integers v w x.val x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' := fun _x _y => Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' := fun _x _y => Subtype.ext (map_add _ _ _)

end IsDedekindDomain.HeightOneSpectrum
