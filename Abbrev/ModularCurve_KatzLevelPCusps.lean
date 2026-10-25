import Mathlib
import Instance.ModularCurve_TateSlots
import Instance.ModularCurve_PhiGen
import Instance.ModularCurve_KatzLevelP

set_option autoImplicit false

noncomputable section

open HahnSeries Polynomial

universe u

namespace ModularCurve

section ToricPoint

variable (R : Type*) [CommRing R] (p : ℕ)

end ToricPoint

section CuspData

variable (R : Type*) [CommRing R] (p : ℕ)

end CuspData

section Twist

variable (R₀ : Type*) [CommRing R₀] {R : Type*} [CommRing R] [Algebra R₀ R]

end Twist

namespace KatzLevelPForm

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} [NeZero p] {k : ℤ}

end KatzLevelPForm

section Cycl

variable (R₀ : Type u) [CommRing R₀] (p : ℕ)

abbrev cyclRing : Type u := AdjoinRoot (Polynomial.cyclotomic p R₀)

end Cycl

namespace KatzGamma0Form

variable {R₀ : Type u} [CommRing R₀] {p : ℕ} [NeZero p] {k : ℤ}

end KatzGamma0Form

end ModularCurve

end
