import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.NumberField.Completion.FiniteLiesOverMaximalIdeal
open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum


/--
[takes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverMaximalIdeal.lean)
-/
@[path]
private lemma takes_eq
  :
-- imply
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
    open scoped NumberField
    /-- Maximal ideal lies over maximal ideal along the adic integer map. -/
    private lemma  comap_maximalIdeal_adicCompletionIntegersMap
    {K L : Type*}
    [Field K]
    [Field L]
    [NumberField K]
    [NumberField L]
    [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    :
    Ideal.comap (adicCompletionIntegersMap v w)
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) =
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
-- proof
  apply takes

/--
[comap_maximalIdeal_adicCompletionIntegersMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FiniteLiesOverMaximalIdeal.lean)
-/
@[path]
private lemma comap_maximalIdeal_adicCompletionIntegersMap_eq
  [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)} [w.asIdeal.LiesOver v.asIdeal] :
-- imply
  Ideal.comap (adicCompletionIntegersMap v w)
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) =
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.comap_maximalIdeal_adicCompletionIntegersMap v w


-- created on 2026-10-20
