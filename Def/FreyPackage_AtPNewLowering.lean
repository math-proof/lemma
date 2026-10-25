import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Def.FLTPrelim_ModularRep
import Def.FreyPackage_LevelRaising
import Def.WeierstrassCurve_PeuRamifiee

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
