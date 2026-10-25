import Mathlib
import sympy.Basic
import Instance.NumberTheory.NumberField.AdeleLocallyCompact.Part2
open IsDedekindDomain NumberField Valued.integer
open scoped Valued Pointwise
open IsDedekindDomain.HeightOneSpectrum


/--
[finite_residueField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/AdeleLocallyCompact.lean)
-/
@[path]
private lemma finite_residueField_eq
  [Field K] [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.finite_residueField K v

/--
[isCompact_adicCompletionIntegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/AdeleLocallyCompact.lean)
-/
@[path]
private lemma isCompact_adicCompletionIntegers_eq
  [Field K] [NumberField K]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  IsCompact (↑(v.adicCompletionIntegers K) : Set (v.adicCompletion K)) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.isCompact_adicCompletionIntegers K v


-- created on 2026-10-20
