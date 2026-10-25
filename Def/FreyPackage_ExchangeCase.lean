import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Def.FLTPrelim_ModularRep
import Instance.FLTPrelim_Modularity
import Def.FLTPrelim_Ramification
import Instance.FreyPackage_GaloisRep
import Def.FreyPackage_LevelRaising
import Def.GaloisRep_GlobalUnramifiedAt
import Instance.FreyPackage_ExchangeCase

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace FreyPackage

def ExchangeCongruence (P : FreyPackage) (q : ℕ) : Prop :=
  (P.p : ℤ) ∣ (q : ℤ) ^ 2 - 1

def ExchangeCaseLowering (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevel N

def MazurPrincipleNewLowering (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N : ℕ, 0 < N → q.Prime → q ≠ 2 → q ≠ P.p → ¬ q ∣ N →
    ¬ P.ExchangeCongruence q →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    P.ModularRepOfLevelNewAt (N * q) q →
    P.ModularRepOfLevel N

end FreyPackage
