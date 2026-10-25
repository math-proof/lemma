import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Instance.FLTPrelim_Modularity

set_option autoImplicit false

noncomputable section

open WeierstrassCurve CuspForm


namespace FreyPackage

open FLTPrelim

def ModularRepOfLevel (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end FreyPackage

namespace WeierstrassCurve

def IsResiduallyModularOfLevel (W : WeierstrassCurve ℤ) (p M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def IsResiduallyModular (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel p M

def IsModularModelOfConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N


def ModRepIsIrreducible (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ
    (W.map (Int.castRingHom ℚ)) n

end WeierstrassCurve

end
