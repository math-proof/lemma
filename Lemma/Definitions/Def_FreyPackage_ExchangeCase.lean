import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_ModularRep
import Lemma.Definitions.Def_FLTPrelim_Modularity
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_FreyPackage_GaloisRep
import Lemma.Definitions.Def_FreyPackage_LevelRaising
import Lemma.Definitions.Def_GaloisRep_GlobalUnramifiedAt

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarExchangeCase :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ExchangeCongruence (P : FreyPackage) (q : ℕ) : Prop :=
  (P.p : ℤ) ∣ (q : ℤ) ^ 2 - 1

instance (P : FreyPackage) (q : ℕ) : Decidable (P.ExchangeCongruence q) :=
  Int.decidableDvd _ _

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
