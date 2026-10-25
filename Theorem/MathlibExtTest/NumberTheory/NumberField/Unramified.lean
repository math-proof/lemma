/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/Unramified.lean -/


import Def.NumberTheory.NumberField.Unramified.Part2
import Lemma.Nat.NumberField.Unramified
open scoped NumberField


noncomputable section

-- Direct application for arbitrary intermediate fields E ≤ F.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (hEF : E ≤ F) (𝔭 : Ideal ℤ) (hF : Algebra.IsUnramifiedIn (𝓞 F) 𝔭) :
    Algebra.IsUnramifiedIn (𝓞 E) 𝔭 :=
  NumberField.isUnramifiedIn_mono E F hEF 𝔭 hF

-- Identity specialization E = F.
example {L : Type*} [Field L] [NumberField L] (E : IntermediateField ℚ L)
    (𝔭 : Ideal ℤ) (h : Algebra.IsUnramifiedIn (𝓞 E) 𝔭) :
    Algebra.IsUnramifiedIn (𝓞 E) 𝔭 :=
  NumberField.isUnramifiedIn_mono E E le_rfl 𝔭 h

-- Pointwise application at a prime lying over 𝔭.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (hEF : E ≤ F) (𝔭 : Ideal ℤ) (hF : Algebra.IsUnramifiedIn (𝓞 F) 𝔭)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver 𝔭] :
    Algebra.IsUnramifiedAt ℤ P :=
  NumberField.isUnramifiedIn_mono E F hEF 𝔭 hF P inferInstance inferInstance

-- Semilocal étaleness above an unramified prime.
example {K : Type*} [Field K] [NumberField K] (p : Ideal ℤ) [p.IsPrime]
    (h : Algebra.IsUnramifiedIn (𝓞 K) p) :
    Algebra.Etale (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)) :=
  NumberField.IsUnramifiedIn.etale_localization p h

-- Semilocal formal unramifiedness via the étale instance.
example {K : Type*} [Field K] [NumberField K] (p : Ideal ℤ) [p.IsPrime]
    (h : Algebra.IsUnramifiedIn (𝓞 K) p) :
    Algebra.FormallyUnramified (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) p.primeCompl)) := by
  have := NumberField.IsUnramifiedIn.etale_localization p h
  infer_instance

-- Semilocal étaleness over ℚ at `⊥`, unramified by `isUnramifiedIn_bot`.
example : Algebra.Etale (Localization.AtPrime (⊥ : Ideal ℤ))
    (Localization
      (Algebra.algebraMapSubmonoid (𝓞 ℚ) (⊥ : Ideal ℤ).primeCompl)) :=
  NumberField.IsUnramifiedIn.etale_localization ⊥ Algebra.isUnramifiedIn_bot

-- Base-change bridge for arbitrary number fields: tensoring the semilocal ring
-- of `F` with that of `E` gives the integral closure in the base-changed ring.
example {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F]
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
    TensorProduct R S_F S_E ≃ₐ[S_F]
      integralClosure S_F (TensorProduct R S_F (FractionRing (𝓞 E))) :=
  NumberField.IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure p h

-- The bridge is `S_F`-linear by definition: it commutes with `algebraMap`.
example {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F]
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (x : Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)) :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
    let e :=
      NumberField.IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure p h
    e (algebraMap S_F (TensorProduct R S_F S_E) x) = algebraMap S_F _ x :=
  (NumberField.IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure p h).commutes
    x

-- Specialization to `⊥` over `ℚ`, unramified by `isUnramifiedIn_bot`.
example :
    let R := Localization.AtPrime (⊥ : Ideal ℤ)
    let S_F :=
      Localization (Algebra.algebraMapSubmonoid (𝓞 ℚ) (⊥ : Ideal ℤ).primeCompl)
    let S_E :=
      Localization (Algebra.algebraMapSubmonoid (𝓞 ℚ) (⊥ : Ideal ℤ).primeCompl)
    TensorProduct R S_F S_E ≃ₐ[S_F]
      integralClosure S_F (TensorProduct R S_F (FractionRing (𝓞 ℚ))) := by
  let _ : (⊥ : Ideal ℤ).IsPrime := Ideal.isPrime_bot
  exact NumberField.IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure ⊥
    Algebra.isUnramifiedIn_bot

-- A localization representative is characterized by cross multiplication in
-- the selected local factor.
example {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver p]
    (x : S) (y : Algebra.algebraMapSubmonoid S p.primeCompl)
    (z : Localization.AtPrime Q) :
    Localization.semilocalizationToAtPrime p Q
        (IsLocalization.mk'
          (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) x y) = z ↔
      algebraMap S (Localization.AtPrime Q) x =
        algebraMap S (Localization.AtPrime Q) y * z :=
  Localization.semilocalizationToAtPrime_mk'_eq_iff p Q x y z

-- Generic semilocal-to-local factor map, direct application.
example {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver p] :
    Localization (Algebra.algebraMapSubmonoid S p.primeCompl) →ₐ[S]
      Localization.AtPrime Q :=
  Localization.semilocalizationToAtPrime p Q

-- Normalized tensor to compositum local factor, direct application.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let C := integralClosure S_F (TensorProduct R S_F (FractionRing (𝓞 E)))
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    C →ₐ[R] T :=
  NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime E F p h Q

-- The selected local-factor map sends a normalized simple tensor to the
-- product of its two semilocal images.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p]
    (x : Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
    (y : Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)) :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
    let M := (E ⊔ F : IntermediateField ℚ L)
    let _algE : Algebra E M := (IntermediateField.inclusion le_sup_left).toAlgebra
    let _algF : Algebra F M := (IntermediateField.inclusion le_sup_right).toAlgebra
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    let fF : S_F →ₐ[𝓞 F] T := Localization.semilocalizationToAtPrime p Q
    let fE : S_E →ₐ[𝓞 E] T := Localization.semilocalizationToAtPrime p Q
    let e := NumberField.IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure
      (E := E) (F := F) p h
    NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime E F p h Q
        (e (x ⊗ₜ[R] y)) = fF x * fE y :=
  NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime_equiv_tmul
    E F p h Q x y

-- Kernel of the compositum local-factor map is prime.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    (RingHom.ker
      (NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime
        E F p h Q).toRingHom).IsPrime :=
  NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime_ker_isPrime
    E F p h Q

-- Contracted-prime membership: an element lies in the contracted prime exactly
-- when its image lies in the maximal ideal of the local target.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p]
    (x : integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E)))) :
    x ∈ NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime E F p h Q ↔
      NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime E F p h Q x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
  NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime_mem_iff E F p h Q x

-- Canonical localization map on a localization representative is characterized
-- by cross multiplication against the base map.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p]
    (x : integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E))))
    (y : (NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime
      E F p h Q).primeCompl)
    (v : Localization.AtPrime Q) :
    NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime
        E F p h Q (IsLocalization.mk'
          (Localization.AtPrime
            (NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime
              E F p h Q)) x y) = v ↔
      NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime E F p h Q x =
        NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime
          E F p h Q ↑y * v :=
  NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime_mk'_spec
    E F p h Q x y v

-- Contracted maximal prime: direct application.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p] :
    (NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime
      E F p h Q).IsPrime :=
  NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime_isPrime E F p h Q

-- Kernel containment in the contracted maximal prime.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    RingHom.ker (NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime
      E F p h Q).toRingHom ≤
      NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime E F p h Q :=
  NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime_ker_le
    E F p h Q

-- Canonical localization map: direct application (a plain `RingHom`).
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p] :
    let qC := NumberField.IsUnramifiedIn.normalizedTensorCompositumPrime E F p h Q
    let S := Localization.AtPrime qC
    let T := Localization.AtPrime Q
    S →+* T :=
  NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime
    E F p h Q

-- Canonical localization map extends the normalized-tensor map.
example {L : Type*} [Field L] [NumberField L] (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L))) [Q.IsPrime] [Q.LiesOver p]
    (x : integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E)))) :
    NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime
        E F p h Q (algebraMap _ _ x) =
      NumberField.IsUnramifiedIn.normalizedTensorToCompositumAtPrime E F p h Q x :=
  NumberField.IsUnramifiedIn.normalizedTensorLocalizationToCompositumAtPrime_algebraMap
    E F p h Q x

end
