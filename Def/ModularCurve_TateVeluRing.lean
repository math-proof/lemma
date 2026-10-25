import Mathlib
import Instance.ModularCurve_TateSlots
import Def.ModularCurve_LaurentCoeff
import Lemma.ModularCurve.KatzLevelPCusps
import Def.WeierstrassCurve_Velu
import Macro.WeierstrassCurve_VeluPointMap
import Def.WeierstrassCurve_VariableChangePointEquiv

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve

namespace ModularCurve.TateVeluRing


section VeluR

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A)

noncomputable def veluXR (S : Finset (A × A)) (x : A) : A :=
  x + ∑ Q ∈ S, (W.veluT Q.1 Q.2 * Ring.inverse (x - Q.1) + W.veluU Q.1 Q.2 * Ring.inverse (x - Q.1) ^ 2)

noncomputable def veluYR (S : Finset (A × A)) (x y : A) : A :=
  y - ∑ Q ∈ S, (W.veluU Q.1 Q.2 * (2 * y + W.a₁ * x + W.a₃) * Ring.inverse (x - Q.1) ^ 3
    + W.veluT Q.1 Q.2 * (W.a₁ * (x - Q.1) + y - Q.2) * Ring.inverse (x - Q.1) ^ 2
    + (W.a₁ * W.veluU Q.1 Q.2 - W.veluGx Q.1 Q.2 * W.veluGy Q.1 Q.2) * Ring.inverse (x - Q.1) ^ 2)

end VeluR

section VcR

variable {A : Type*} [CommRing A]

def vcXInvR (C : WeierstrassCurve.VariableChange A) (x : A) : A := ((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)

def vcYInvR (C : WeierstrassCurve.VariableChange A) (x y : A) : A :=
  ((C.u⁻¹ : Aˣ) : A) ^ 3 * (y - C.t - C.s * (x - C.r))

end VcR

section LaurentUnits

variable {A : Type*} [CommRing A]


def toricXCoeff (p : ℕ) (c : Aˣ) (m : ℕ) : A :=
  if m = 0 then (c : A) * Ring.inverse (1 - (c : A)) ^ 2
  else (∑ d ∈ m.divisors, if p ∣ d then
          ((m / d : ℕ) : A) * ((c : A) ^ (m / d) + ((c⁻¹ : Aˣ) : A) ^ (m / d)) else 0)
    - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : A) else 0)

end LaurentUnits

end ModularCurve.TateVeluRing

end
