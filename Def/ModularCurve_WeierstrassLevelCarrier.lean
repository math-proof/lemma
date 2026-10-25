import Mathlib

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type*} [CommRing T] (W : WeierstrassCurve T)

def smulNumerator (a d : ℕ) (h : T[X]) : T[X] :=
  ∑ i ∈ Finset.range (d + 1), C (h.coeff i) * W.Φ a ^ i * W.ΨSq a ^ (d - i)


def kernelVariableChange (C : VariableChange T) (h : T[X]) : T[X] :=
  Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * h.natDegree)) * h.comp (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r)

def jOfUnit (hΔ : IsUnit W.Δ) : T :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  W.j

end WeierstrassCurve

end
