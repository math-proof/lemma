import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.Unramified.Part2
open NumberField
open Localization
open IsUnramifiedIn


namespace NumberField

/--
[isUnramifiedIn_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma isUnramifiedIn_mono
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {𝔭 : Ideal ℤ}
-- given
  (hEF : E ≤ F)
  (hF : Algebra.IsUnramifiedIn (𝓞 F) 𝔭) :
-- imply
  Algebra.IsUnramifiedIn (𝓞 E) 𝔭 := by
-- proof
  let _alg : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  intro P hP hPE
  obtain ⟨Q, _, hQprime, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F) P ⊥
      (Ideal.comap_bot_le_of_injective _
        (NumberField.RingOfIntegers.algebraMap.injective E F))
  have hQP' : Q.LiesOver P := ⟨hQP.symm⟩
  have hQp : Q.LiesOver 𝔭 := ⟨by rw [hPE.over, hQP'.over, Ideal.under_under]⟩
  have hQ : Algebra.IsUnramifiedAt ℤ Q := hF Q hQprime hQp
  let _ : Q.IsPrime := hQprime
  let _ : Q.LiesOver P := hQP'
  let _ : Algebra.IsUnramifiedAt ℤ Q := hQ
  exact Algebra.IsUnramifiedAt.of_liesOver ℤ P Q

end NumberField

namespace Localization

/--
[semilocalizationToAtPrime_mk'_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma semilocalizationToAtPrime_mk'_eq_iff
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
  rw [semilocalizationToAtPrime, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_mk'_spec]
  change algebraMap S (Localization.AtPrime Q) x =
    algebraMap S (Localization.AtPrime Q) y * z ↔ _
  rfl
end Localization
namespace NumberField
variable {L : Type*} [Field L] [NumberField L]
namespace IsUnramifiedIn


namespace NumberField.IsUnramifiedIn

/--
[normalizedTensorToCompositumAtPrime_equiv_tmul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma normalizedTensorToCompositumAtPrime_equiv_tmul
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
  dsimp
  simp [normalizedTensorToCompositumAtPrime]
  congr 1

end NumberField.IsUnramifiedIn

namespace NumberField.IsUnramifiedIn

/--
[normalizedTensorToCompositumAtPrime_ker_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma normalizedTensorToCompositumAtPrime_ker_isPrime
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  let R := by
-- proof
  dsimp
  exact RingHom.ker_isPrime _

end NumberField.IsUnramifiedIn

namespace NumberField.IsUnramifiedIn

/--
[normalizedTensorCompositumPrime_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma normalizedTensorCompositumPrime_mem_iff
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
  unfold normalizedTensorCompositumPrime
  rfl

end NumberField.IsUnramifiedIn

namespace NumberField.IsUnramifiedIn

/--
[normalizedTensorToCompositumAtPrime_ker_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma normalizedTensorToCompositumAtPrime_ker_le
  [Field L] [NumberField L]
  {E F : IntermediateField ℚ L}
  {p : Ideal ℤ} [p.IsPrime]
  {Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))} [Q.IsPrime] [Q.LiesOver p]
-- given
  (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
-- imply
  let R := by
-- proof
  unfold normalizedTensorCompositumPrime
  exact Ideal.ker_le_comap _

end NumberField.IsUnramifiedIn

namespace NumberField.IsUnramifiedIn

/--
[normalizedTensorLocalizationToCompositumAtPrime_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma normalizedTensorLocalizationToCompositumAtPrime_algebraMap
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
  unfold normalizedTensorLocalizationToCompositumAtPrime
  rw [IsLocalization.lift_eq]
  rfl

end NumberField.IsUnramifiedIn

namespace NumberField.IsUnramifiedIn

/--
[normalizedTensorLocalizationToCompositumAtPrime_mk'_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean)
-/
@[path]
lemma normalizedTensorLocalizationToCompositumAtPrime_mk'_spec
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
  unfold normalizedTensorLocalizationToCompositumAtPrime
  rwa [IsLocalization.lift_mk'_spec]
end IsUnramifiedIn
end NumberField


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


-- created on 2026-10-20
-- updated on 2026-10-23
