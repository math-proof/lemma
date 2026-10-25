import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Instance.FLTPrelim_Modularity
import Def.FLTPrelim_ModularRep
import Def.FLTPrelim_Ramification
import Instance.FreyPackage_ExchangeCase
import Def.GaloisRep_GlobalUnramifiedAt
import Instance.FreyPackage_GaloisRep
import Def.FreyPackage_LevelRaising
import Def.RibetLevelLowering_CharacterGroupApparatusV2
import Def.WeierstrassCurve_PeuRamifiee
import Def.FreyPackage_AtPNewLowering

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
