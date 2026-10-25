import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)

abbrev HH : Type := (i : Fin g) → ZMod (δ i)

namespace Heis

variable {δ} {d}

end Heis

section Schrodinger

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

end Schrodinger

section Matrices

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) (B : Type) [CommRing B] (ω : B) {n : ℕ} (e : Fin n ≃ HH δ)

end Matrices

end AlgebraicGeometry.ThetaLevel

end
