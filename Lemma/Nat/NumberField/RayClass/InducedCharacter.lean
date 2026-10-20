import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.InducedCharacter
open scoped nonZeroDivisors
open NumberField
open Modulus


/--
[finiteExponent_le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma finiteExponent_le_of_dvd_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)}
-- given
  (h : m1 ∣ m2) :
-- imply
  finiteExponent m1 v ≤ finiteExponent m2 v := by
-- proof
  apply NumberField.Modulus.finiteExponent_le_of_dvd h v

/--
[IsRayElementOne.of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma IsRayElementOne_of_dvd_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {x : Kˣ}
-- given
  (h : m1 ∣ m2)
  (hx : IsRayElementOne m2 x) :
-- imply
  IsRayElementOne m1 x := by
-- proof
  apply NumberField.Modulus.IsRayElementOne.of_dvd h hx

/--
[rayGenerators_map_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma rayGenerators_map_of_dvd_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {y : coprimeFractionalIdeals m2}
-- given
  (h : m1 ∣ m2)
  (hy : y ∈ rayGenerators m2) :
-- imply
  coprimeInclusion h y ∈ rayGroup m1 := by
-- proof
  apply NumberField.Modulus.rayGenerators_map_of_dvd h y hy

/--
[rayGroup_le_comap_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma rayGroup_le_comap_of_dvd_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
-- given
  (h : m1 ∣ m2) :
-- imply
  rayGroup m2 ≤ (rayGroup m1).comap (coprimeInclusion h) := by
-- proof
  apply NumberField.Modulus.rayGroup_le_comap_of_dvd h

/--
[RayClassGroup.mapOfDvd_rayClassMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma RayClassGroup_mapOfDvd_rayClassMap_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {x : coprimeFractionalIdeals m2}
-- given
  (h : m1 ∣ m2) :
-- imply
  mapOfDvd h (rayClassMap m2 x) = rayClassMap m1 (coprimeInclusion h x) := by
-- proof
  apply NumberField.Modulus.RayClassGroup.mapOfDvd_rayClassMap h x

/--
[RayClassCharacter.isInducedBy_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma RayClassCharacter_isInducedBy_iff_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {chi2 : RayClassCharacter m2}
  {chi1 : RayClassCharacter m1}
-- given
  (h : m1 ∣ m2) :
-- imply
  chi2.IsInducedBy chi1 h ↔ ∀ x : coprimeFractionalIdeals m2,
    pullback chi2 x = pullback chi1 (coprimeInclusion h x) := by
-- proof
  apply NumberField.Modulus.RayClassCharacter.isInducedBy_iff chi2 chi1 h

/--
[RayClassCharacter.isPrimitive_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/InducedCharacter.lean)
-/
@[path]
private lemma RayClassCharacter_isPrimitive_iff_eq
  [Field K] [NumberField K]
  {m1 m2 : Modulus K}
  {chi : RayClassCharacter m2} :
-- imply
  chi.IsPrimitive ↔ ∀ (m0 : Modulus K) (chi0 : RayClassCharacter m0)
    (h : m0 ∣ m2), chi = chi0.comp (RayClassGroup.mapOfDvd h) → m0 = m2 := by
-- proof
  apply NumberField.Modulus.RayClassCharacter.isPrimitive_iff chi


-- created on 2026-10-20
