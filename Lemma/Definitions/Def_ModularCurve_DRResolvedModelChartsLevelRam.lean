import Mathlib
import Lemma.Definitions.Def_ModularCurve_DRResolvedModelPackageLevelRam
import Lemma.Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

noncomputable section

namespace ModularCurve

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRResolvedModelPackageLevelRam

variable {hqN : ¬ q ∣ N₀} {𝔛 : DRModelPackageLevel N₀ q hqN} {O : Type} [CommRing O] {ρO : DRLevel.R q →+* O} {ϖ : O}
  {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackageLevelRam N₀ q 𝔛 O ρO ϖ κ toκ)

def crossingPt (n : 𝔛reg.node) : ↥(DRLevel.XO (N₀ := N₀) ρO) :=
  (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base (𝔛reg.nodeEquiv n)

structure DRResolvedModelChartsLevelRam (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData) where
  U : 𝔛reg.node → (DRLevel.XO (N₀ := N₀) ρO).Opens
  mem_U : ∀ n, 𝔛reg.crossingPt n ∈ U n
  not_mem_U : ∀ n m, m ≠ n → 𝔛reg.crossingPt m ∉ U n
  f : ∀ n, (U n).toScheme ⟶ crossingScheme (ϖ ^ 𝔛reg.width n)
  etale : ∀ n, Etale (f n)
  f_over : ∀ n, f n ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (ϖ ^ 𝔛reg.width n)))) =
    (U n).ι ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))
  f_mem_Vc_iff : ∀ n (y : U n),
    (f n).base y ∈ ((PrimeSpectrum.basicOpen (CrossingQuotient.U (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens) ⊔
      (PrimeSpectrum.basicOpen (CrossingQuotient.V (ϖ ^ 𝔛reg.width n)) : (crossingScheme (ϖ ^ 𝔛reg.width n)).Opens)) ↔
      (y : ↥(DRLevel.XO (N₀ := N₀) ρO)) ≠ 𝔛reg.crossingPt n
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
    (𝔛reg.comp (DRResolvedModelPackageLevel.chainPos 𝔛reg.width n d)).comap (𝔛reg.toDR ⁻¹ᵁ (U n)).ι =
      (Fc (𝔛reg.width n) d).comap (g n)

attribute [instance] DRResolvedModelChartsLevelRam.etale

end DRResolvedModelPackageLevelRam

end ModularCurve

end
