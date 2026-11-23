module

public import Theorem.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Def.FLTPrelim_ModularRep
public import Def.FreyPackage_LevelRaising
public import Def.WeierstrassCurve_PeuRamifiee

@[expose] public section

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
