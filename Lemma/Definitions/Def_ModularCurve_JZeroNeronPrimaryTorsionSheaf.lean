import Mathlib
import Lemma.Definitions.Def_ModularCurve_JZeroNeronDataPrime
import Lemma.Definitions.Def_ModularCurve_EisensteinIdeal
import Lemma.Definitions.Def_ModularCurve_FppfKummerInterface
import Lemma.Definitions.Def_ModularCurve_MazurStepThreeInputs
import Lemma.Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Lemma.Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Lemma.Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Lemma.Definitions.Def_ModularCurve_JZeroToricTorsion

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

instance eisensteinMaximalIdeal.isPrime (N q : ℕ) [Fact q.Prime] :
    (eisensteinMaximalIdeal N q).IsPrime := by
  have hq : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  exact Ideal.IsPrime.comap _

abbrev eisensteinPrimaryTorsionBar (p q m : ℕ) [NeZero p] : AddSubgroup (JZero p) :=
  letI := heckeModuleBar p
  (AddMonoidHom.ker ((q ^ m : ℤ) • AddMonoidHom.id (JZero p))) ⊓
    ⨆ k : ℕ, (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup

abbrev toricEisensteinPrimaryPart (p q : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime p) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroToricTorsion p A (q ^ m) ⊓ eisensteinPrimaryTorsionBar p q m

abbrev eisensteinQuotientRationalLocalized (p q : ℕ) [NeZero p] [Fact q.Prime] : Type :=
  letI := heckeModuleBar p
  LocalizedModule (eisensteinMaximalIdeal p q).primeCompl
    ↥(Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)))

theorem torsionBySet_eisensteinMaximalIdeal_pow_le_eisensteinPrimaryTorsionBar
    (p q m : ℕ) [NeZero p] :
    letI := heckeModuleBar p
    (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg)).toAddSubgroup
      ≤ eisensteinPrimaryTorsionBar p q m := by
  letI := heckeModuleBar p
  intro x hx
  refine ⟨?_, ?_⟩
  · have hq : ((q : HeckeAlg) ^ m) ∈ (eisensteinMaximalIdeal p q) ^ m := by
      apply Ideal.pow_mem_pow
      simp [eisensteinMaximalIdeal, Ideal.mem_comap]
    have hx' : ((q : HeckeAlg) ^ m) • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨_, hq⟩
    change ((q : ℤ) ^ m) • x = 0
    rw [← Int.cast_smul_eq_zsmul HeckeAlg]
    simpa [Int.cast_pow, Int.cast_natCast] using hx'
  · exact AddSubgroup.mem_iSup_of_mem m hx

structure JZeroNeronPrimaryTorsionCore (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
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
  genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ) ≃ ↥(eisensteinPrimaryTorsionBar p q m)
  genericConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    genericPoints m (f * g) = genericPoints m f + genericPoints m g
  genericGalois : ∀ m, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, g h = σ (f h)) →
    ((genericPoints m g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = σ • ((genericPoints m f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
  Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1}
  incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)
  proj : ∀ m, 𝒥 (m + 1) ⟶ Q m
  incl_proj : ∀ m, incl m ≫ proj m = 0
  ses_shortExact : ∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact
  pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPrimaryPart p q A hA m)
  pFibreConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A),
    pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g
  pFibreGenericCompat : ∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A),
    ∀ ψ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, ψ h = A.subtype (φ h)) →
    ((pFibrePoints m φ : ↥(toricEisensteinPrimaryPart p q A hA m)) : JZero p)
      = ((genericPoints m ψ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)

  kummerRow : ∀ m, JKummerRow q m (eisensteinQuotientRationalLocalized p q)

  kummerRow_H1Jtors : ∀ m,
    letI := (kummerRow m).instH1Jtors;
    (kummerRow m).H1Jtors ≃+ fppfCohomology specInt (𝒥 m) 1

attribute [instance] JZeroNeronPrimaryTorsionCore.instCommRing_H
  JZeroNeronPrimaryTorsionCore.instHopfAlgebra_H
  JZeroNeronPrimaryTorsionCore.instFiniteType_H JZeroNeronPrimaryTorsionCore.instFlat_H

structure JZeroNeronPrimaryTorsionFFModels (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) where
  Hff : ∀ (_m : ℕ) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → Type
  [instCommRing_Hff : ∀ m ℓ hℓ hℓp, CommRing (Hff m ℓ hℓ hℓp)]
  [instHopfAlgebra_Hff : ∀ m ℓ hℓ hℓp, HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instFinite_Hff : ∀ m ℓ hℓ hℓp, Module.Finite (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instFlat_Hff : ∀ m ℓ hℓ hℓp, Module.Flat (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instCocomm_Hff : ∀ m ℓ hℓ hℓp, Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  ffPoints : ∀ m ℓ hℓ hℓp, WithConv (Hff m ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)
    ≃ ↥(eisensteinPrimaryTorsionBar p q m)
  ffConv : ∀ m ℓ hℓ hℓp, ∀ f g, ffPoints m ℓ hℓ hℓp (f * g)
    = ffPoints m ℓ hℓ hℓp f + ffPoints m ℓ hℓ hℓp g
  ffGalois : ∀ m ℓ hℓ hℓp, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (Hff m ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
    (∀ h, g h = σ (f h)) →
    ((ffPoints m ℓ hℓ hℓp g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = σ • ((ffPoints m ℓ hℓ hℓp f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
  HffBarQ : ∀ (_m : ℕ), q ≠ p → Type
  [instCommRing_HffBarQ : ∀ m hqp, CommRing (HffBarQ m hqp)]
  [instHopfAlgebra_HffBarQ : ∀ m hqp, HopfAlgebra (ZMod q) (HffBarQ m hqp)]
  [instFinite_HffBarQ : ∀ m hqp, Module.Finite (ZMod q) (HffBarQ m hqp)]
  [instCocomm_HffBarQ : ∀ m hqp, Coalgebra.IsCocomm (ZMod q) (HffBarQ m hqp)]
  ffBarQ_red : ∀ m hqp, Hff m q Fact.out hqp →+* HffBarQ m hqp
  ffBarQ_red_surjective : ∀ m hqp, Function.Surjective (ffBarQ_red m hqp)
  ffBarQ_red_ker : ∀ m hqp, RingHom.ker (ffBarQ_red m hqp)
    = Ideal.span {((q : ℤ) : Hff m q Fact.out hqp)}

attribute [instance] JZeroNeronPrimaryTorsionFFModels.instCommRing_Hff
  JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_Hff JZeroNeronPrimaryTorsionFFModels.instFinite_Hff
  JZeroNeronPrimaryTorsionFFModels.instFlat_Hff JZeroNeronPrimaryTorsionFFModels.instCocomm_Hff
  JZeroNeronPrimaryTorsionFFModels.instCommRing_HffBarQ JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_HffBarQ
  JZeroNeronPrimaryTorsionFFModels.instFinite_HffBarQ JZeroNeronPrimaryTorsionFFModels.instCocomm_HffBarQ

structure JZeroNeronPrimaryTorsionInvPins (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (F : JZeroNeronPrimaryTorsionFFModels p q A hA C) where
  inv : ℕ → AdmissibleInvariants q
  h0_pin : ∀ m, Nat.card (fppfCohomology specInt (C.𝒥 m) 0) = q ^ (inv m).h0
  h1_pin : ∀ m, Nat.card (fppfCohomology specInt (C.𝒥 m) 1) = q ^ (inv m).h1
  δ_pin : ∀ m, Nat.card ↥(eisensteinPrimaryTorsionBar p q m)
    = q ^ (inv m).δ * Nat.card ↥(toricEisensteinPrimaryPart p q A hA m)
  α_pin : ∀ m, ∀ hqp : q ≠ p,
    Nat.card (WithConv (F.HffBarQ m hqp →ₐ[ZMod q] AlgebraicClosure (ZMod q))) = q ^ (inv m).α

structure JZeroNeronPrimaryTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) where
  core : JZeroNeronPrimaryTorsionCore p q A hA
  ffModels : JZeroNeronPrimaryTorsionFFModels p q A hA core
  invPins : JZeroNeronPrimaryTorsionInvPins p q A hA core ffModels

def HasJZeroNeronPrimaryTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
    Nonempty (JZeroNeronPrimaryTorsionSheaf p q A hA)

section Falseprobe

end Falseprobe

end ModularCurve

end
