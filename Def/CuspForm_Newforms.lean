import Def.FreyPackage_LevelRaising
import Instance.FLTPrelim_GaloisRep
import Instance.CuspForm_Newforms

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point
open ModularFormClass

namespace CuspForm

variable {N : ℕ}

def GoodEigensystemOccursAt (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (M : ℕ) : Prop :=
  ∃ g : CuspForm (CongruenceSubgroup.Gamma0 M) 2, g.IsNormalizedEigenform ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff g ℓ = qCoeff f ℓ


def IsNewform (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  f.IsNormalizedEigenform ∧ ∀ M : ℕ, M ∣ N → M ≠ N → ¬ GoodEigensystemOccursAt f M


def IsNewformAt (q : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  f.IsNormalizedEigenform ∧ q ∣ N ∧ ¬ GoodEigensystemOccursAt f (N / q)


variable (N) in

def NewformBadPrimeCoeff : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f.IsNewform →
    ∀ q : ℕ, q.Prime → q ∣ N →
      (¬ q ^ 2 ∣ N → qCoeff f q ^ 2 = 1) ∧ (q ^ 2 ∣ N → qCoeff f q = 0)

end CuspForm

namespace FreyPackage

open CuspForm

def ModularRepOfNewLevelLE (P : FreyPackage) (N M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNewform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def CongruenceEnlargement (P : FreyPackage) : Prop :=
  ∀ N M : ℕ, M ∣ N → 0 < M →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.ModularRepOfNewLevelLE N M → P.ModularRepOfNewLevelLE M M

end FreyPackage

end
