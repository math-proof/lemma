import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Instance.FLTPrelim_Modularity
import Def.FLTPrelim_ModularRep
import Def.FLTPrelim_Ramification
import Def.FreyPackage_LevelRaising
import Def.RibetLevelLowering_CharacterGroupApparatusV2
import Def.GaloisRep_GlobalUnramifiedAt
import Instance.FreyPackage_GaloisRep
import Instance.FreyPackage_ExchangeCase
import Def.FreyPackage_LoweringAt
import Def.FreyPackage_AtPNewLowering
import Def.WeierstrassCurve_PeuRamifiee
import Def.WeierstrassCurve_Semistability

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point FreyCurve

open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarUniformPin :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ModularRepOfLevelNewAtPinned (P : FreyPackage) (M q : ℕ) : Prop :=
  ∃ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    g.IsNormalizedEigenform ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    (∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪) ∧
    g.IsNewAt q

def MazurPrincipleNewLoweringAtUniform (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAtPinned (N * q) q →
    P.ModularRepOfLevelAt N

def ExchangeCaseLoweringAtUniform (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAtPinned (N * q) q →
    P.ModularRepOfLevelAt N

def AtPNewLoweringAtUniform (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAtPinned (N₀ * P.p) P.p →
    P.ModularRepOfLevelAt N₀

end FreyPackage

end
