import Mathlib
import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FreyPackage_LevelRaising
import Lemma.Definitions.Def_FreyPackage_GaloisRep
import Lemma.Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Lemma.Definitions.Def_ModularCurve_HeckeModule
import Lemma.Definitions.Def_ModularCurve_HeckeInputsAll
import Lemma.Definitions.Def_ModularCurve_MazurPrincipleCore

set_option autoImplicit false

noncomputable section

namespace FreyPackage

open ModularCurve
open scoped CongruenceSubgroup

abbrev mazurGaloisGroup : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

structure EigenformIdealData (P : FreyPackage) (M : ℕ) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (𝔪 : Ideal HeckeAlg) : Prop where
  hmax : 𝔪.IsMaximal
  hpmem : ((P.p : ℕ) : HeckeAlg) ∈ 𝔪
  heis : ¬ IsEventuallyEisenstein 𝔪
  heigen : ∀ (ℓ : Nat.Primes) (b : ℤ), (algebraMap ℤ ℂ b = ModularFormClass.qCoeff g ℓ) →
    heckeGen ℓ - MvPolynomial.C b ∈ 𝔪

def IdealGoodPrimeCurveCongruence (p M : ℕ) (W : WeierstrassCurve ℤ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
    heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪

def IsAttachedMatrixRep (𝔪 : Ideal HeckeAlg) (Sρ : Finset ℕ)
    (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)) : Prop :=
  ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ℓ ∉ Sρ →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρmat σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρmat σ).det

def IsAttachedMatrixRepWithOpenKer (𝔪 : Ideal HeckeAlg) (Sρ : Finset ℕ)
    (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)) : Prop :=
  IsAttachedMatrixRep 𝔪 Sρ ρmat ∧ IsOpen (ρmat.ker : Set mazurGaloisGroup)

def AttachedRepUnramifiedAtQ (q : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∀ (Sρ : Finset ℕ) (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)),
    IsAttachedMatrixRepWithOpenKer 𝔪 Sρ ρmat → IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρmat σ = 1) ∧
        ∀ frob : mazurGaloisGroup, A.IsFrobeniusAt frob q → (ρmat frob).det = ((q : ℕ) : HeckeAlg ⧸ 𝔪)

def CurveAttachmentMatrixData (P : FreyPackage) (q N : ℕ) [NeZero q] [NeZero N]
    [Module HeckeAlg (JZero (N * q))] (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (c : mazurGaloisGroup),
    (∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ℓ ∉ ((N * q) * P.p).primeFactors →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).trace = Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩))
    ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ ((N * q) * P.p).primeFactors →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).det = ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪))
    ∧ (∀ Wsub : Submodule (HeckeAlg ⧸ 𝔪) (Fin 2 → HeckeAlg ⧸ 𝔪),
        (∀ g, ∀ v ∈ Wsub, (ρmat g).mulVec v ∈ Wsub) → Wsub = ⊥ ∨ Wsub = ⊤)
    ∧ ρmat c * ρmat c = 1
    ∧ (ρmat c).det = -1
    ∧ ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker
        ∧ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
             fixingSubgroup mazurGaloisGroup
               (heckeTorsion (JZero (N * q)) 𝔪 : Set (JZero (N * q)))

def MazurPerWitnessIdealSupplyFamily (P : FreyPackage) (q : ℕ) [NeZero q] : Prop :=
  ∀ (N : ℕ) [NeZero N], ¬ q ∣ N →
    WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 (N * q)) 2) (𝔪w : Ideal (integralClosure ℤ ℂ)),
      P.IsCongruentWitness (N * q) g (freyCurveInt P) 𝔪w → g.IsNewAt q →
      HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
      ∃ 𝔪 : Ideal HeckeAlg,
        P.EigenformIdealData (N * q) g 𝔪 ∧
        IdealGoodPrimeCurveCongruence P.p (N * q) (freyCurveInt P) 𝔪 ∧
        AttachedRepUnramifiedAtQ q 𝔪 ∧
        (letI := heckeModuleBar (N * q)
         P.CurveAttachmentMatrixData q N 𝔪 ∧ heckeTorsion (JZero (N * q)) 𝔪 ≠ ⊥)

end FreyPackage

end
