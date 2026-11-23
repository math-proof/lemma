module

public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Instance.FLTPrelim_Modularity
public import Def.FLTPrelim_ModularRep
public import Def.FLTPrelim_Ramification
public import Def.FreyPackage_LevelRaising
public import Def.RibetLevelLowering_CharacterGroupApparatusV2
public import Def.GaloisRep_GlobalUnramifiedAt
public import Instance.FreyPackage_GaloisRep
public import Instance.FreyPackage_ExchangeCase
public import Def.FreyPackage_LoweringAt
public import Def.FreyPackage_AtPNewLowering
public import Def.WeierstrassCurve_PeuRamifiee
public import Def.WeierstrassCurve_Semistability

@[expose] public section

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
