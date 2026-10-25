import Mathlib

set_option autoImplicit false

namespace HopfAlgebra.KummerRadicands

variable {O : Type*} [CommRing O] {n : ℕ} {t : ℕ} (u : Fin t → Oˣ)

def rad (k : Fin t → ZMod n) : Oˣ := ∏ i, u i ^ (k i).val

def carry (k k' : Fin t → ZMod n) : Oˣ := ∏ i, (u i)⁻¹ ^ (((k i).val + (k' i).val) / n)

end HopfAlgebra.KummerRadicands
