module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.RingTheory.DedekindDomain.AdicCompletionResidueField.Part2
open IsDedekindDomain
open scoped Valued
open IsDedekindDomain.HeightOneSpectrum


public section

/--
[ker_completionResidueMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicCompletionResidueField.lean)
-/
@[path]
private theorem ker_completionResidueMap_eq
  [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {𝔭 : HeightOneSpectrum A} :
-- imply
  RingHom.ker (𝔭.completionResidueMap (K := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.ker_completionResidueMap 𝔭

/--
[surjective_completionResidueMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicCompletionResidueField.lean)
-/
@[path]
private theorem surjective_completionResidueMap_eq
  [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {𝔭 : HeightOneSpectrum A} :
-- imply
  Function.Surjective (𝔭.completionResidueMap (K := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.surjective_completionResidueMap 𝔭


-- created on 2026-10-20
