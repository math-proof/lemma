import Mathlib
import Structure.ModularCurve_JZeroNeronDataPrime
import Def.ModularCurve_EisensteinIdeal
import Structure.ModularCurve_FppfKummerInterface
import Def.ModularCurve_MazurStepThreeInputs
import Instance.AlgebraicGeometry_FppfSiteCohomology
import Instance.AlgebraicGeometry_FppfCohomologyLES
import Instance.AlgebraicGeometry_FppfKummerProp17
import Def.ModularCurve_JZeroToricTorsion
import Abbrev.ModularCurve_JZeroNeronTorsionSheafV4

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite


structure JZeroNeronTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) where

  𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1}

  H : ℕ → Type
  [instCommRing_H : ∀ m, CommRing (H m)]
  [instHopfAlgebra_H : ∀ m, HopfAlgebra ℤ (H m)]
  [instFiniteType_H : ∀ m, Algebra.FiniteType ℤ (H m)]
  [instFlat_H : ∀ m, Module.Flat ℤ (H m)]

  ff_finite : ∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))

  sectionsEquiv : ∀ (m : ℕ) (U : specInt.Fppf),
    (𝒥 m).1.obj (op U) ≃+ Additive (WithConv (H m →ₐ[ℤ] Γ(U.left, ⊤)))

  sectionsNat : ∀ (m : ℕ) {U V : specInt.Fppf} (f : U ⟶ V) (s : (𝒥 m).1.obj (op V)),
    ∀ h : H m,
      (Additive.toMul (sectionsEquiv m U ((𝒥 m).1.map f.op s))) h
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (sectionsEquiv m V s)) h)

  genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ) ≃ ↥(eisensteinTorsionBar p q m)

  genericConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    genericPoints m (f * g) = genericPoints m f + genericPoints m g

  genericGalois : ∀ m, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, g h = σ (f h)) →
    ((genericPoints m g : ↥(eisensteinTorsionBar p q m)) : JZero p)
      = σ • ((genericPoints m f : ↥(eisensteinTorsionBar p q m)) : JZero p)

  pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPart p q A hA m)

  pFibreConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A),
    pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g

  pFibreGenericCompat : ∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A),
    ∀ ψ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, ψ h = A.subtype (φ h)) →
    ((pFibrePoints m φ : ↥(toricEisensteinPart p q A hA m)) : JZero p)
      = ((genericPoints m ψ : ↥(eisensteinTorsionBar p q m)) : JZero p)

  Hff : ∀ (_m : ℕ) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → Type
  [instCommRing_Hff : ∀ m ℓ hℓ hℓp, CommRing (Hff m ℓ hℓ hℓp)]
  [instHopfAlgebra_Hff : ∀ m ℓ hℓ hℓp, HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instFinite_Hff : ∀ m ℓ hℓ hℓp, Module.Finite (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instFlat_Hff : ∀ m ℓ hℓ hℓp, Module.Flat (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instCocomm_Hff : ∀ m ℓ hℓ hℓp, Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]

  ffPoints : ∀ m ℓ hℓ hℓp, WithConv (Hff m ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)
    ≃ ↥(eisensteinTorsionBar p q m)

  ffConv : ∀ m ℓ hℓ hℓp, ∀ f g, ffPoints m ℓ hℓ hℓp (f * g)
    = ffPoints m ℓ hℓ hℓp f + ffPoints m ℓ hℓ hℓp g

  ffGalois : ∀ m ℓ hℓ hℓp, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (Hff m ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
    (∀ h, g h = σ (f h)) →
    ((ffPoints m ℓ hℓ hℓp g : ↥(eisensteinTorsionBar p q m)) : JZero p)
      = σ • ((ffPoints m ℓ hℓ hℓp f : ↥(eisensteinTorsionBar p q m)) : JZero p)

  Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1}

  incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)

  proj : ∀ m, 𝒥 (m + 1) ⟶ Q m

  incl_proj : ∀ m, incl m ≫ proj m = 0

  ses_shortExact : ∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact

  inv : ℕ → AdmissibleInvariants q

  h0_pin : ∀ m, Nat.card (fppfCohomology specInt (𝒥 m) 0) = q ^ (inv m).h0

  h1_pin : ∀ m, Nat.card (fppfCohomology specInt (𝒥 m) 1) = q ^ (inv m).h1

  δ_pin : ∀ m, Nat.card ↥(eisensteinTorsionBar p q m)
    = q ^ (inv m).δ * Nat.card ↥(toricEisensteinPart p q A hA m)

  HffBarQ : ∀ (_m : ℕ), q ≠ p → Type
  [instCommRing_HffBarQ : ∀ m hqp, CommRing (HffBarQ m hqp)]
  [instHopfAlgebra_HffBarQ : ∀ m hqp, HopfAlgebra (ZMod q) (HffBarQ m hqp)]
  [instFinite_HffBarQ : ∀ m hqp, Module.Finite (ZMod q) (HffBarQ m hqp)]
  [instCocomm_HffBarQ : ∀ m hqp, Coalgebra.IsCocomm (ZMod q) (HffBarQ m hqp)]

  ffBarQ_red : ∀ m hqp, Hff m q Fact.out hqp →+* HffBarQ m hqp

  ffBarQ_red_surjective : ∀ m hqp, Function.Surjective (ffBarQ_red m hqp)

  ffBarQ_red_ker : ∀ m hqp, RingHom.ker (ffBarQ_red m hqp)
    = Ideal.span {((q : ℤ) : Hff m q Fact.out hqp)}

  α_pin : ∀ m, ∀ hqp : q ≠ p,
    Nat.card (WithConv (HffBarQ m hqp →ₐ[ZMod q] AlgebraicClosure (ZMod q))) = q ^ (inv m).α

  kummerRow : ∀ m,
    letI := heckeModuleBar p
    JKummerRow q m ↥(AddSubgroup.closure (eisensteinQuotientRational p (heckeModuleBar p)))

  kummerRow_H1Jtors : ∀ m,
    letI := heckeModuleBar p; letI := (kummerRow m).instH1Jtors;
    (kummerRow m).H1Jtors ≃+ fppfCohomology specInt (𝒥 m) 1

attribute [instance] JZeroNeronTorsionSheaf.instCommRing_H JZeroNeronTorsionSheaf.instHopfAlgebra_H
  JZeroNeronTorsionSheaf.instFiniteType_H JZeroNeronTorsionSheaf.instFlat_H
  JZeroNeronTorsionSheaf.instCommRing_Hff JZeroNeronTorsionSheaf.instHopfAlgebra_Hff
  JZeroNeronTorsionSheaf.instFinite_Hff JZeroNeronTorsionSheaf.instFlat_Hff
  JZeroNeronTorsionSheaf.instCocomm_Hff
  JZeroNeronTorsionSheaf.instCommRing_HffBarQ JZeroNeronTorsionSheaf.instHopfAlgebra_HffBarQ
  JZeroNeronTorsionSheaf.instFinite_HffBarQ JZeroNeronTorsionSheaf.instCocomm_HffBarQ


section Falseprobe

end Falseprobe

end ModularCurve

end
