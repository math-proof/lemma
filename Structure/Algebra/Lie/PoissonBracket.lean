module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Prime
/-!
# Poisson brackets over commutative `ℂ`-algebras

Poisson-bracket interface over commutative `ℂ`-algebras: brackets,
Poisson ideals and primes, Poisson cores with their universal
property, and basic closure lemmas.
-/


public noncomputable section

namespace Poisson

/-- Poisson-bracket data: the bracket with bilinearity, skew-symmetry,
the Leibniz rule, the Jacobi identity, and `ℂ`-bilinearity over a
complex algebra structure. -/
structure PoissonBracket (A : Type*) [CommRing A] [Algebra ℂ A] where
  bracket : A → A → A
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  skew : ∀ x y, bracket x y = -bracket y x
  leibniz : ∀ x y z, bracket x (y * z) = y * bracket x z + bracket x y * z
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) +
      bracket z (bracket x y) = 0
  smul_left : ∀ (c : ℂ) (x y : A),
    bracket (c • x) y = c • bracket x y
  smul_right : ∀ (c : ℂ) (x y : A),
    bracket x (c • y) = c • bracket x y

end Poisson
end
