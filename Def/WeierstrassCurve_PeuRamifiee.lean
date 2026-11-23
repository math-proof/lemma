module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Def.ModularCurve_AtPPackage

@[expose] public section

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
