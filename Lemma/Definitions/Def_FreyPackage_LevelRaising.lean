import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Lemma.Definitions.Def_FLTPrelim_ModularRep

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace CuspForm

def IsNewAt {M : ℕ} (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) : Prop :=
  ModularFormClass.qCoeff g q ^ 2 = 1

end CuspForm

namespace FreyPackage

noncomputable local instance instDecEqQbarLevelRaising :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def IsCongruentWitness (P : FreyPackage) (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) : Prop :=
  f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def ModularRepOfLevelNewAt (P : FreyPackage) (M q : ℕ) : Prop :=
  ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)), P.IsCongruentWitness M g W 𝔪 ∧ g.IsNewAt q

def LevelRaising (P : FreyPackage) (N q' : ℕ) : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)),
    0 < N → q'.Prime → ¬ q' ∣ N → q' ≠ P.p →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.IsCongruentWitness N f W 𝔪 →
    (∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f q' ∧
      a ^ 2 - ((q' : integralClosure ℤ ℂ) + 1) ^ 2 ∈ 𝔪) →
    P.ModularRepOfLevelNewAt (N * q') q'

end FreyPackage
