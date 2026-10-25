import Mathlib
import Instance.AlgebraicGeometry_ThetaLevelGroup

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)


structure Heis : Type where
  a : ZMod (2 * d)
  h : HH δ
  k : HH δ

namespace Heis

variable {δ} {d}


variable (δ d) in


end Heis

section Schrodinger

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)


end Schrodinger

section Matrices

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) (B : Type) [CommRing B] (ω : B) {n : ℕ} (e : Fin n ≃ HH δ)


end Matrices

end AlgebraicGeometry.ThetaLevel

end
