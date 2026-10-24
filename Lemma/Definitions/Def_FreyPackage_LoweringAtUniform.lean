import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_Modularity
import Lemma.Definitions.Def_FLTPrelim_ModularRep
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_FreyPackage_LevelRaising
import Lemma.Definitions.Def_RibetLevelLowering_CharacterGroupApparatusV2
import Lemma.Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Lemma.Definitions.Def_FreyPackage_GaloisRep
import Lemma.Definitions.Def_FreyPackage_ExchangeCase
import Lemma.Definitions.Def_FreyPackage_LoweringAt
import Lemma.Definitions.Def_FreyPackage_AtPNewLowering
import Lemma.Definitions.Def_WeierstrassCurve_PeuRamifiee
import Lemma.Definitions.Def_WeierstrassCurve_Semistability

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
