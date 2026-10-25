import Mathlib
import Instance.AlgebraicGeometry_ProjSpaceCechTwist

set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

section Carrier

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}
variable (D : GradedModule R n)

end Carrier

section GradSec

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n) (I : Finset (Fin (n + 1)))


end GradSec

section GradAltC

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

end GradAltC

section SecInclIrrel

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

end SecInclIrrel

section Instances

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}


end Instances

section FD

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}

end FD

section SubMod

variable {R : Type u} [CommRing R] {n : ℕ}

end SubMod

section Hom

variable {R : Type u} [CommRing R] {n : ℕ}


variable {D₁ D₂ : GradedModule R n}

end Hom

section IsFG

variable {R : Type u} [CommRing R] {n : ℕ}


abbrev GradedModule.IsFG (D : GradedModule R n) : Prop := Nonempty (GradedModule.Presentation D)

end IsFG

section HomShift

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}


end HomShift

end ProjSpaceCech

end
