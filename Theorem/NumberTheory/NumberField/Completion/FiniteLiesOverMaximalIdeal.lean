/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverMaximalIdeal.lean -/

import Def.NumberTheory.NumberField.Completion.FiniteLiesOverValuation
import Lemma.Nat.NumberField.Completion.FiniteLiesOverValuation
/-!
# Finite place completion maximal ideal lies over

## ATLAS source correspondence

This is a canonical-map specialization of
`completion_maximalIdeal_comap` at atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`, lines 2192--2229](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L2192-L2229).
That source
theorem takes Dedekind domains `A ⊆ B`, fraction fields `K ⊆ L`, finite and
separable `L/K`, primes `𝔭` and `𝔮` with `𝔮` over `𝔭`, arbitrary algebra
structures on the two completion integer rings, and an explicit compatibility
hypothesis saying their integer-ring algebra map has the same underlying map as
the completion-field algebra map. It concludes that the upstairs maximal ideal
contracts to the downstairs maximal ideal.

Here the clause-by-clause specialization is:

* `A = 𝓞 K` and `B = 𝓞 L`; the two `NumberField` instances and `[Algebra K L]`
  provide the source Dedekind-domain, fraction-field, finite-dimensional,
  separability, integral-closure, and scalar-tower setting.
* `v` and `w` are the source height-one primes `𝔭` and `𝔮`; the instance
  `[w.asIdeal.LiesOver v.asIdeal]` is its `𝔮`-over-`𝔭` hypothesis.
* `adicCompletionIntegersMap v w`, constructed in the preceding #967 stage,
  replaces the source's arbitrary algebra map. The #967 theorem
  `adicCompletionIntegersMap_apply` discharges the source compatibility
  hypothesis by identifying its underlying map with `adicCompletionMap v w`.
* `comap_maximalIdeal_adicCompletionIntegersMap` is exactly the source
  contraction conclusion for that canonical map.

The proof uses the stronger canonical valuation formula from #967:
`v_w(map x) = v_v(x) ^ e(w/v)`. Since `e(w/v) ≠ 0`, being a nonunit (valuation
different from one) is preserved and reflected, yielding equality of maximal
ideals. This proves only the contraction prerequisite; residue-field
equivalences and degree formulas remain outside this module.
-/


namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Maximal ideal lies over maximal ideal along the adic integer map. -/
theorem comap_maximalIdeal_adicCompletionIntegersMap :
    Ideal.comap (adicCompletionIntegersMap v w)
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  ext x
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v (adicCompletionMap v w (x : v.adicCompletion K)) ≠ 1 ↔
    Valued.v (x : v.adicCompletion K) ≠ 1
  rw [valuation_adicCompletionMap]
  exact not_congr (pow_eq_one_iff_of_nonneg
    (show (0 : WithZero (Multiplicative ℤ)) ≤
      Valued.v (x : v.adicCompletion K) from bot_le)
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
      w.asIdeal v.ne_bot))

end IsDedekindDomain.HeightOneSpectrum
