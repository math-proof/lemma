/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Unramified.lean -/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Instances
import Theorem.NumberTheory.NumberField.Unramified


namespace NumberField

variable {L : Type*} [Field L] [NumberField L]

/-- Global normalization base-change bridge above an unramified prime: for number
fields `E` and `F` and `p` unramified in `𝓞 F`, tensoring the semilocal
integral-closure identification of `E` with the semilocal ring of `F` identifies
`S_F ⊗[R] S_E` with the integral closure of `S_F` in the base-changed fraction
ring.

This is the normalization-under-étale-base-change route toward the compositum
step `baseChange_ramificationIdx_eq_one` and `isUnramifiedAtPrime_sup` in the
primary Lean source for ATLAS N390. The local-factor/compositum identification
needed to recover those source theorems is not claimed here. -/
noncomputable def IsUnramifiedIn.tensorProductLocalizationEquivIntegralClosure
    {E F : Type*} [Field E] [NumberField E] [Field F] [NumberField F]
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p) :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
    TensorProduct R S_F S_E ≃ₐ[S_F]
      integralClosure S_F (TensorProduct R S_F (FractionRing (𝓞 E))) := by
  let R := Localization.AtPrime p
  let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
  let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
  let _ : Algebra.Etale R S_F := IsUnramifiedIn.etale_localization p h
  letI : Algebra S_E (FractionRing (𝓞 E)) :=
    Localization.AtPrime.liftAlgebra (𝓞 E)
  let e : S_E ≃ₐ[R] integralClosure R (FractionRing (𝓞 E)) :=
    IsIntegralClosure.equiv R S_E (FractionRing (𝓞 E)) _
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : S_F ≃ₐ[S_F] S_F) e).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S_F
      (FractionRing (𝓞 E))) TensorProduct.toIntegralClosure_bijective_of_smooth)

end NumberField

namespace Localization

/-- Semilocal-to-local factor map: localize the semilocal ring away from `p`
further at the prime `Q` lying over `p`. -/
noncomputable def semilocalizationToAtPrime
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime] (Q : Ideal T) [Q.IsPrime] [Q.LiesOver p] :
    Localization (Algebra.algebraMapSubmonoid S p.primeCompl) →ₐ[S]
      Localization.AtPrime Q :=
  IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := Q.primeCompl)
        (Localization.AtPrime Q) ⟨algebraMap R T x, by
          simp_all [Q.over_def p]
        ⟩)

end Localization

namespace NumberField

namespace IsUnramifiedIn

/-- This maps the normalized tensor algebra to the local ring at `Q` and
selects the compositum component, but does NOT yet claim the induced
localization is an equivalence.

It is the normalized, prime-selected map corresponding to the fixed-`Q` stage
of `baseChange_ramificationIdx_eq_one` in the primary Lean source for ATLAS
N390. -/
noncomputable def normalizedTensorToCompositumAtPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    let R := Localization.AtPrime p
    let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
    let C := integralClosure S_F
      (TensorProduct R S_F (FractionRing (𝓞 E)))
    let T := Localization.AtPrime Q
    letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
    C →ₐ[R] T := by
  let R := Localization.AtPrime p
  let S_F := Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl)
  let S_E := Localization (Algebra.algebraMapSubmonoid (𝓞 E) p.primeCompl)
  let M := (E ⊔ F : IntermediateField ℚ L)
  let _algE : Algebra E M := (IntermediateField.inclusion le_sup_left).toAlgebra
  let _algF : Algebra F M := (IntermediateField.inclusion le_sup_right).toAlgebra
  let T := Localization.AtPrime Q
  letI : Algebra R T := Localization.AtPrime.algebraOfLiesOver p Q
  let fF : S_F →ₐ[𝓞 F] T := Localization.semilocalizationToAtPrime _ _
  let fE : S_E →ₐ[𝓞 E] T := Localization.semilocalizationToAtPrime _ _
  algebraize [fF.toRingHom, fE.toRingHom]
  letI : IsScalarTower R S_F T := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext z
    simp
  letI : IsScalarTower R S_E T := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext z
    simp
  let g : TensorProduct R S_F S_E →ₐ[R] T :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S_F T)
      (IsScalarTower.toAlgHom R S_E T) fun _ _ => .all _ _
  let e := tensorProductLocalizationEquivIntegralClosure
    (E := E) (F := F) p h
  exact g.comp (e.symm.restrictScalars R).toAlgHom

/-- Contracted maximal prime: the correct prime of the normalized tensor algebra
at which to localize to obtain the local factor `Localization.AtPrime Q`.

Let `g := normalizedTensorToCompositumAtPrime E F p h Q` and
`T := Localization.AtPrime Q`. This is the comap of the maximal ideal of the
local ring `T` under `g`. It contains the prime kernel of `g` (see
`normalizedTensorToCompositumAtPrime_ker_le`), but it is in general strictly
larger: for a nonzero prime below `Q`, a nonzero uniformizer lies outside
`RingHom.ker g` yet maps to a nonunit of `T`.

This is a named alternative-normalization prerequisite stage for the missing
`cyclotomic_ramIdx_eq_of_unramified` and
[`baseChange_ramificationIdx_eq_one`, lines 1549--1586](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean#L1549-L1586)
in the primary Lean source for ATLAS `NumberTheoryI` target N390,
Proposition 19.14. It does not prove
compositum unramifiedness, any `IsLocalization` identification, or the final
maximality theorem. -/
noncomputable def normalizedTensorCompositumPrime
    (E F : IntermediateField ℚ L)
    (p : Ideal ℤ) [p.IsPrime] (h : Algebra.IsUnramifiedIn (𝓞 F) p)
    (Q : Ideal (𝓞 (E ⊔ F : IntermediateField ℚ L)))
    [Q.IsPrime] [Q.LiesOver p] :
    Ideal (integralClosure
      (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
      (TensorProduct (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid (𝓞 F) p.primeCompl))
        (FractionRing (𝓞 E)))) :=
  let T := Localization.AtPrime Q
  letI : Algebra (Localization.AtPrime p) T :=
    Localization.AtPrime.algebraOfLiesOver p Q
  (IsLocalRing.maximalIdeal T).comap
    (normalizedTensorToCompositumAtPrime E F p h Q).toRingHom

end IsUnramifiedIn
end NumberField
