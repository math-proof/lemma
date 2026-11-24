module
public import Mathlib
public import Instance.WeierstrassCurve_Generic
public import Abbrev.WeierstrassCurve_Generic
set_option autoImplicit false


public section

universe u v

noncomputable section

open MvPolynomial

namespace WeierstrassCurve.Generic

section CommRing

variable (K : Type u) [CommRing K]

def poly : WeierstrassCurve (MvPolynomial (Fin 5) K) :=
  ⟨X 0, X 1, X 2, X 3, X 4⟩

variable {K}

section coeffs

variable {A : Type v}

def coeffs (W : WeierstrassCurve A) : Fin 5 → A := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

end coeffs

variable {A : Type v} [CommRing A] [Algebra K A]

variable (K) in

def classify (W : WeierstrassCurve A) : MvPolynomial (Fin 5) K →ₐ[K] A :=
  MvPolynomial.aeval (coeffs W)


end CommRing

section Field

variable (K : Type u) [Field K]

def curve : WeierstrassCurve (Closure K) :=
  (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K))

end Field

end WeierstrassCurve.Generic

end
