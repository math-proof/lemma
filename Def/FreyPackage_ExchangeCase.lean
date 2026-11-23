module

public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Def.FLTPrelim_ModularRep
public import Instance.FLTPrelim_Modularity
public import Def.FLTPrelim_Ramification
public import Instance.FreyPackage_GaloisRep
public import Def.FreyPackage_LevelRaising
public import Def.GaloisRep_GlobalUnramifiedAt
public import Instance.FreyPackage_ExchangeCase

@[expose] public section

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
