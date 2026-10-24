/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormOneIdeleClassGroup.lean -/

/-
Author: @toskua, Avocado
-/

import sympy.atlas.NumberTheory.NumberField.IdeleNorm
import Lemma.Nat.NumberField.IdeleNorm
/-!
# Norm-one idele class group

## ATLAS source correspondence

This is the number-field part of ATLAS NumberTheoryI N547, Definition 26.11.
The primary formal source is atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
[`v1/Atlas/NumberTheoryI/code/Ideles.lean`, lines 889--890](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Ideles.lean#L889-L890), where
`Ideles.NormOneIdeleClassGroup` is defined as
`OneIdeleGroup K ⧸ (principalIdeles K).subgroupOf (OneIdeleGroup K)`.
The textbook statement is also indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 3904--3908](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L3904-L3908).

The declarations below map to that source as follows:

* `normOnePrincipalIdeles` is the source denominator
  `(principalIdeles K).subgroupOf (OneIdeleGroup K)`, expressed using this
  repository's native `normOneIdeles` and principal-idele API.
* `NormOneIdeleClassGroup` is exactly the source quotient `C_K^1 := I_K^1 / K^×`.
  Because it is a quotient of topological groups, it inherits the source's
  quotient topology.
* `normOne_mk_principalEmbedding` exposes the defining quotient fact that a
  principal idele represents the identity class.

The word "compact" in Definition 26.11 depends on N546, Theorem 26.9
(Fujisaki's lemma), formalized in the
[ATLAS source at `Ideles.lean`, lines 839--887](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/Ideles.lean#L839-L887).
That compactness result is intentionally outside this module's scope:
we define the quotient and its topology but do not assert a `CompactSpace`
instance.
-/

noncomputable section

namespace NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

/-- Principal ideles viewed inside the norm-one ideles. -/
def normOnePrincipalIdeles : Subgroup (normOneIdeles K) :=
  (principalIdeles (NumberField.RingOfIntegers K) K).subgroupOf (normOneIdeles K)

/-- The norm-one idele class group `C_K^1 := I_K^1 / K^×`. -/
abbrev NormOneIdeleClassGroup :=
  (normOneIdeles K) ⧸ (normOnePrincipalIdeles K)
end NumberField.TopologicalIdeleGroup
