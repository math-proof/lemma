import Mathlib
import Instance.ModularCurve_KatzLevelP

set_option autoImplicit false

universe u

namespace ModularCurve

def IsNormalForm {T : Type u} [CommRing T] (ℓ : ℕ) (W : WeierstrassCurve T) (D : LevelPData T) : Prop :=
  if ℓ = 3 then
    W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0 ∧ D.xP = 0 ∧ D.yP = 0 ∧ D.xQ = D.yQ
  else
    W.a₄ = 0 ∧ W.a₆ = 0 ∧ W.a₂ = W.a₃ ∧ D.xP = 0 ∧ D.yP = 0

end ModularCurve
