import Mathlib
import Lemma.Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Lemma.Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

noncomputable section

namespace ModularCurve

variable {p : ℕ} [Fact p.Prime]

namespace DRResolvedModelPackage

variable {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

def crossingPt (n : 𝔛reg.node) : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) :=
  (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)

structure DRResolvedModelCharts (ϖ : O) (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData) where
  U : 𝔛reg.node → (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens
  mem_U : ∀ n, 𝔛reg.crossingPt n ∈ U n
  not_mem_U : ∀ n m, m ≠ n → 𝔛reg.crossingPt m ∉ U n
  f : ∀ n, (U n).toScheme ⟶ crossingScheme (ϖ ^ 𝔛reg.width n)
  etale : ∀ n, Etale (f n)
  f_over : ∀ n, f n ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ 𝔛reg.width n)))) =
    (U n).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  f_mem_Vc_iff : ∀ n (y : U n),
    (f n).base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens) ⊔
      (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens)) ↔
      (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) ≠ 𝔛reg.crossingPt n
  hinj : ∀ n (y y' : ↥(pullback (f n) (Resolution.toCrossing ϖ (𝔛reg.width n)))),
    ((pullback.fst (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y).1 = 𝔛reg.crossingPt n →
      ((pullback.fst (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y').1 = 𝔛reg.crossingPt n →
        (pullback.snd (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y =
          (pullback.snd (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))).base y' → y = y'
  g : ∀ n, (𝔛reg.toDR ⁻¹ᵁ (U n)).toScheme ⟶ Resolution ϖ (𝔛reg.width n)
  Φ : ∀ n, pullback (f n) (Resolution.toCrossing ϖ (𝔛reg.width n)) ≅ (𝔛reg.toDR ⁻¹ᵁ (U n)).toScheme
  Φ_fst : ∀ n, (Φ n).hom ≫ (𝔛reg.toDR ∣_ U n) = pullback.fst (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))
  Φ_snd : ∀ n, (Φ n).hom ≫ g n = pullback.snd (f n) (Resolution.toCrossing ϖ (𝔛reg.width n))
  label : ∀ n (d : Fin (𝔛reg.width n + 1)),
    (𝔛reg.comp (DRResolvedModelPackage.chainPos 𝔛reg.width n d)).comap (𝔛reg.toDR ⁻¹ᵁ (U n)).ι =
      (Fc (𝔛reg.width n) d).comap (g n)

attribute [instance] DRResolvedModelCharts.etale

end DRResolvedModelPackage

end ModularCurve

end
