import Mathlib
import Lemma.Submodule.Repartitions

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

abbrev LSpace (D : Divisor K F) : Submodule K F := riemannRochSpace D

abbrev ell (D : Divisor K F) : ℕ := Module.finrank K (LSpace D)

structure RiemannGenusReachedAt (γ : ℤ) (D₀ : Divisor K F) : Prop where
  finite : FiniteDimensional K (LSpace D₀)
  eq : Divisor.degree D₀ - (ell D₀ : ℤ) = γ - 1
  isMax : ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ - 1

end AlgebraicCurve

end
