module

public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Instance.FLTPrelim_Modularity
public import Def.FLTPrelim_ModularRep
public import Def.FLTPrelim_Ramification
public import Instance.FreyPackage_ExchangeCase
public import Def.GaloisRep_GlobalUnramifiedAt
public import Instance.FreyPackage_GaloisRep
public import Def.FreyPackage_LevelRaising
public import Def.RibetLevelLowering_CharacterGroupApparatusV2
public import Def.WeierstrassCurve_PeuRamifiee
public import Def.FreyPackage_AtPNewLowering

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine.Point

set_option autoImplicit false

noncomputable section

namespace FreyPackage

noncomputable local instance instDecEqQbarDescentRepoint :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def MazurPrincipleNewLoweringAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevelAt N

def ExchangeCaseLoweringAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevelAt N

def AtPNewLoweringAt (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAt (N₀ * P.p) P.p →
    P.ModularRepOfLevelAt N₀

end FreyPackage

end
