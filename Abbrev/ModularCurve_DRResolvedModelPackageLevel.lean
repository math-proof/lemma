import Mathlib
import Structure.ModularCurve_DRModelPackageLevel
import Abbrev.ModularCurve_X0MqResolvedTable
import Def.AlgebraicCurve_RelCartier
import Structure.ModularCurve_DRResolvedModelPackageLevel

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve.IgusaScheme

namespace ModularCurve

attribute [local instance] DRModelPackageLevel.neZero_mul


namespace DRLevel

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime]

abbrev XO {O : Type} [CommRing O] (ρ : R q →+* O) : Scheme.{0} :=
  pullback (toBase N₀ q) (Spec.map (CommRingCat.ofHom ρ))


end DRLevel

open DRLevel


end ModularCurve

end
