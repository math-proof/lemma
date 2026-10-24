/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TrinomialTransformSequence.lean -/

import sympy.atlas.NumberTheory.TrinomialCoefficient
/-!
# Trinomial transform sequence

This module defines the sequence transform whose weights are the trinomial
coefficients from the prerequisite API.
-/

namespace MetaMathlibExt

open scoped BigOperators

/-- The trinomial transform of `a`, with the `n`th row weighted by the
coefficients of `(1 + X + X²)ⁿ`.

Concept `jis_sem_ddbad39a52886299b21344a6`; source statement
`jis_1961e690ee22a57370a48a96` from László Németh, *The Trinomial Transform
Triangle*, Journal of Integer Sequences 21 (2018), Article 18.7.3. -/
noncomputable def trinomialTransformSequence {R : Type*} [Semiring R]
    (a : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (2 * n + 1), (trinomialCoefficient n i : R) * a i
end MetaMathlibExt
