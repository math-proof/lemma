import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Lemma.Definitions.Def_ModularCurve_AtPPackage

open scoped Classical in
section

namespace WeierstrassCurve

def IsPeuRamifieeAt (W : WeierstrassCurve ℚ) (p ℓ : ℕ) : Prop :=
  (p : ℤ) ∣ padicValRat ℓ W.Δ

end WeierstrassCurve

namespace ModularCurve

def peuRamifieeGuard (W : WeierstrassCurve ℚ) (p ℓ : ℕ) : Ideal HeckeAlg → Prop :=
  fun _ => W.IsPeuRamifieeAt p ℓ

end ModularCurve

end
