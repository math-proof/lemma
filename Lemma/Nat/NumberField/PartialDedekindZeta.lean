import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.PartialDedekindZeta
open NumberField


/--
[partialDedekindZeta_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PartialDedekindZeta.lean)
-/
@[path]
private lemma partialDedekindZeta_empty_eq
  [Field K] [NumberField K]
  {s : ℂ} :
-- imply
  partialDedekindZeta K ∅ s = 1 := by
-- proof
  apply NumberField.partialDedekindZeta_empty K s

/--
[partialDedekindZeta_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PartialDedekindZeta.lean)
-/
@[path]
private lemma partialDedekindZeta_singleton_eq
  [Field K] [NumberField K]
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K)}
  {s : ℂ} :
-- imply
  partialDedekindZeta K {𝔭} s =
      (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))⁻¹ := by
-- proof
  apply NumberField.partialDedekindZeta_singleton K 𝔭 s


-- created on 2026-10-20
