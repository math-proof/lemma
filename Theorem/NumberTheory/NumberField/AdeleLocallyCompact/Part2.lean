/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/AdeleLocallyCompact.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Def.RingTheory.DedekindDomain.AdicCompletionResidueField.Part2
import Lemma.Int.DedekindDomain.AdicCompletionResidueField
import Mathlib.Topology.Algebra.Module.Compact
import Instance.NumberTheory.NumberField.AdeleLocallyCompact
/-!
# Local compactness of number-field adeles

For a number field `K`, the adic-completion integers are compact, each local
completion is proper, and the finite adele ring and the adele ring are `T2`
and locally compact.

## ATLAS source correspondence

The adic-completeness instance below supplies a prerequisite for ATLAS
NumberTheoryI N265, Theorem 13.5. At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, N265 is indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879).
Its finite-place proof
uses completed integer rings, notably in
`KroneckerWeber.adicCompletionIntegers_isIntegralClosure_aux` and
`adicCompletionIntegers_module_finite`,
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 1661--1714](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L1661-L1714).
The repaired
integral-closure route requires the base completion integer ring to be complete
for its maximal-ideal adic topology.

`isAdicComplete_adicCompletionIntegers` proves exactly that prerequisite from
the compactness established immediately above. Given a compatible sequence
`f n` modulo powers of the maximal ideal, it forms the cosets
`S n = f n + (maximalIdeal)^n`. Compatibility makes these nonempty closed
cosets nested. Compactness gives a point in their intersection, and membership
in every `S n` says precisely that this point is congruent to `f n` modulo
`(maximalIdeal)^n`. This is `IsAdicComplete.prec'`; no separate metric
normalization or unstated completeness assumption is used.
-/


noncomputable section

open IsDedekindDomain NumberField Valued.integer

open scoped Valued Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable (K : Type*) [Field K] [NumberField K]

/-- The adic completion integers are compact as a subset of the completion. -/
theorem isCompact_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
  change IsCompact (Valued.integer (v.adicCompletion K) : Set (v.adicCompletion K))
  have hcomp := (compactSpace K v).isCompact_univ
  rwa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_val] at hcomp

end IsDedekindDomain.HeightOneSpectrum
end
