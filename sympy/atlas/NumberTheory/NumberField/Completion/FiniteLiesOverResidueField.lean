/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverResidueField.lean -/

import sympy.atlas.NumberTheory.NumberField.Completion.FiniteLiesOverMaximalIdeal
/-!
# Naturality of adic integer maps with ring-of-integers algebra maps

## ATLAS source correspondence

This is the pre-quotient commutative square used in
`completion_residueFieldEquiv_compat` at atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 2248--2318](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2248-L2318).
In that
source, `A` and its integral closure `B` map vertically to their completed
integer rings at primes `𝔭` and `𝔮`; after quotienting by the two maximal
ideals, lines 2267--2278 assert that the induced residue-field square commutes.
The elementwise heart of the proof is the
[equality at lines 2291--2305](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2291-L2305)
between
the two routes from `A` to the upstairs completed integer ring.

Here `A = 𝓞 K`, `B = 𝓞 L`, `𝔭 = v`, and `𝔮 = w`. The four corners before
quotienting are

```
𝓞 K  ───────────────→  𝓞 L
 │                       │
 ▼                       ▼
v.adicCompletionIntegers K ─→ w.adicCompletionIntegers L.
```

The top and vertical arrows are the displayed `algebraMap`s, while the bottom
arrow is the canonical `adicCompletionIntegersMap v w` constructed in #967.
`adicCompletionIntegersMap_algebraMap` states exactly that the two composites
from the upper-left to lower-right corner agree. The `NumberField` and
`[Algebra K L]` assumptions specialize the source's Dedekind-domain,
integral-closure, fraction-field, finite-separable, and scalar-tower context;
`[w.asIdeal.LiesOver v.asIdeal]` specializes `𝔮 ∣ 𝔭`.

Together with #977's equality of contracted maximal ideals, this square
descends to the
[quotient/residue-field square in source lines 2267--2278](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2267-L2278).
That
naturality is then used by
[`completion_residueField_finrank_eq` (starting at line 2324)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2324),
one of the finite-place local-degree ingredients supporting N265,
Theorem 13.5. This module proves neither the quotient equivalence nor the final
tensor-product decomposition itself.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Naturality of the adic integer map with respect to ring-of-integers maps. -/
theorem adicCompletionIntegersMap_algebraMap (a : 𝓞 K) :
    (adicCompletionIntegersMap v w)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) =
      algebraMap (𝓞 L) (w.adicCompletionIntegers L)
        (algebraMap (𝓞 K) (𝓞 L) a) := by
  apply Subtype.ext
  change adicCompletionMap v w
      (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a)) =
    algebraMap L (w.adicCompletion L)
      (algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) a))
  rw [adicCompletionMap_algebraMap,
    IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
  congr 1

end IsDedekindDomain.HeightOneSpectrum

-- End of file.
