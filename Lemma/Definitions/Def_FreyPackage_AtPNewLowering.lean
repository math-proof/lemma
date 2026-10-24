import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_ModularRep
import Lemma.Definitions.Def_FreyPackage_LevelRaising
import Lemma.Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option autoImplicit false

noncomputable section

open WeierstrassCurve.Affine.Point

namespace FreyPackage

noncomputable local instance instDecEqQbarLedgerStageFour :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def AtPNewLowering (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAt (N₀ * P.p) P.p →
    P.ModularRepOfLevel N₀

end FreyPackage

end
