import Mathlib
import Abbrev.ModularCurve_DRModelPackageLevel
import Def.ModularCurve_X0MqResolvedTable
import Def.AlgebraicCurve_RelCartier
import Structure.ModularCurve_DRResolvedModelPackageLevel
import Structure.ModularCurve_DRResolvedModelPackageLevelRam

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul

namespace DRLevel


theorem unifOn_natCast {O : Type} [CommRing O] {Y : Scheme.{0}} (toBase : Y ⟶ Spec (CommRingCat.of O)) (n : ℕ)
    (U : Y.affineOpens) : unifOn toBase (n : O) U = (n : Γ(Y, U)) := by
  simp [unifOn, map_natCast]

end DRLevel

open DRLevel


def DRResolvedModelPackageLevelRam.ofUnramified {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} {𝔛 : DRModelPackageLevel N₀ q hqN}
    {O : Type} [CommRing O] {ρ : R q →+* O} {κ : Type} [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (𝔜 : DRResolvedModelPackageLevel N₀ q 𝔛 O ρ κ toκ) : DRResolvedModelPackageLevelRam N₀ q 𝔛 O ρ ((q : ℕ) : O) κ toκ :=
  { 𝔜 with comp_prod := fun U => (𝔜.comp_prod U).trans (by rw [DRLevel.unifOn_natCast]) }

end ModularCurve

end
