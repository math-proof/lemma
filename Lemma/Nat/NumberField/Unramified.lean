import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Unramified
open NumberField
open Localization
open IsUnramifiedIn


/--
[isUnramifiedIn_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma isUnramifiedIn_mono_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {𝔭 : Ideal ℤ}
-- given
  (hEF : E ≤ F)
  (hF : Algebra.IsUnramifiedIn (𝓞 F) 𝔭) :
-- imply
  Algebra.IsUnramifiedIn (𝓞 E) 𝔭 := by
-- proof
  apply NumberField.isUnramifiedIn_mono E F hEF 𝔭 hF

/--
[IsUnramifiedIn.etale_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma IsUnramifiedIn_etale_localization_eq
  [Field L] [NumberField L] [Field K] [NumberField K]
  {p : Ideal ℤ} [p.IsPrime]
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 K) p) :
-- imply
  Algebra.Etale (Localization.AtPrime p)
    (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)) := by
-- proof
  apply NumberField.IsUnramifiedIn.etale_localization p h

/--
[semilocalizationToAtPrime_mk'_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma semilocalizationToAtPrime_mk'_eq_iff_eq
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  {p : Ideal R} [p.IsPrime]
  {Q : Ideal T} [Q.IsPrime] [Q.LiesOver p]
  {x : S}
  {y : Algebra.algebraMapSubmonoid S p.primeCompl}
  {z : Localization.AtPrime Q} :
-- imply
  semilocalizationToAtPrime p Q
    (IsLocalization.mk'
    (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) x y) = z ↔
    algebraMap S (Localization.AtPrime Q) x =
    algebraMap S (Localization.AtPrime Q) y * z := by
-- proof
  apply Localization.semilocalizationToAtPrime_mk'_eq_iff p Q x y z

/--
[normalizedTensorToCompositumAtPrime_equiv_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorToCompositumAtPrime_equiv_tmul_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
  {x : Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)}
  {y : Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)}
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  let R := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime_equiv_tmul E F p h Q x y

/--
[normalizedTensorToCompositumAtPrime_ker_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorToCompositumAtPrime_ker_isPrime_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  let R := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime_ker_isPrime E F p h Q

/--
[normalizedTensorCompositumPrime_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorCompositumPrime_isPrime_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  (normalizedTensorCompositumPrime E F p h Q).IsPrime := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime_isPrime E F p h Q

/--
[normalizedTensorCompositumPrime_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorCompositumPrime_mem_iff_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
  {x : integralClosure (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) (TensorProduct (Localization.AtPrime p) (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) (FractionRing (𝓞 E)))}
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  x ∈ normalizedTensorCompositumPrime E F p h Q ↔
    normalizedTensorToCompositumAtPrime E F p h Q x ∈
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime_mem_iff E F p h Q x

/--
[normalizedTensorToCompositumAtPrime_ker_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorToCompositumAtPrime_ker_le_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  let R := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime_ker_le E F p h Q

/--
[normalizedTensorLocalizationToCompositumAtPrime_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorLocalizationToCompositumAtPrime_algebraMap_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
  {x : integralClosure (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) (TensorProduct (Localization.AtPrime p) (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) (FractionRing (𝓞 E)))}
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  normalizedTensorLocalizationToCompositumAtPrime E F p h Q
    (algebraMap _ _ x) =
    normalizedTensorToCompositumAtPrime E F p h Q x := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime_algebraMap E F p h Q x

/--
[normalizedTensorLocalizationToCompositumAtPrime_mk'_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
private lemma normalizedTensorLocalizationToCompositumAtPrime_mk'_spec_eq
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
  {x : integralClosure (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) (TensorProduct (Localization.AtPrime p) (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) (FractionRing (𝓞 E)))}
  {y : (normalizedTensorCompositumPrime E F p h Q).primeCompl}
  {v : Localization.AtPrime Q}
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  normalizedTensorLocalizationToCompositumAtPrime E F p h Q
    (IsLocalization.mk'
    (Localization.AtPrime (normalizedTensorCompositumPrime E F p h Q)) x y) =
    v ↔
    normalizedTensorToCompositumAtPrime E F p h Q x =
    normalizedTensorToCompositumAtPrime E F p h Q ↑y * v := by
-- proof
  apply NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime_mk'_spec E F p h Q x y v


-- created on 2026-10-20
