import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ResidueFieldHelper
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum


/--
[ker_completionResidueMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldHelper.lean)
-/
@[path]
private lemma ker_completionResidueMap_eq
  [CommRing A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {𝔭 : HeightOneSpectrum A} :
-- imply
  RingHom.ker (𝔭.completionResidueMap (K := K)) = 𝔭.asIdeal := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.ker_completionResidueMap 𝔭

/--
[exists_mul_sub_mem_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldHelper.lean)
-/
@[path]
private lemma exists_mul_sub_mem_of_not_mem_eq
  [CommRing A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {𝔭 : HeightOneSpectrum A}
  {b : A}
-- given
  (hb : b ∉ 𝔭.asIdeal) :
-- imply
  ∃ e : A, b * e - 1 ∈ 𝔭.asIdeal := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.exists_mul_sub_mem_of_not_mem 𝔭 b hb

/--
[surj_completionResidueMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldHelper.lean)
-/
@[path]
private lemma surj_completionResidueMap_eq
  [CommRing A]
  [IsDedekindDomain A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {𝔭 : HeightOneSpectrum A} :
-- imply
  Function.Surjective (𝔭.completionResidueMap (K := K)) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.surj_completionResidueMap 𝔭


-- created on 2026-10-23
