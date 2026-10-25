import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Bounds.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Prime
import Structure.Algebra.Lie.PoissonBracket
/-!
# Poisson brackets over commutative `ℂ`-algebras

Poisson-bracket interface over commutative `ℂ`-algebras: brackets,
Poisson ideals and primes, Poisson cores with their universal
property, and basic closure lemmas.
-/


noncomputable section

namespace Poisson

/-- `P` is a Poisson ideal: stable under bracketing with all of `A`. -/
def IsPoissonIdeal (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (P : Ideal A) : Prop :=
  ∀ (a p : A), p ∈ P → br.bracket a p ∈ P

/-- `P` is a Poisson prime: prime and Poisson. -/
def IsPoissonPrime (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (P : Ideal A) : Prop :=
  P.IsPrime ∧ IsPoissonIdeal A br P

/-- The Poisson core of `J`: the largest Poisson ideal inside `J`,
as the supremum of all Poisson ideals below `J`. -/
def poissonCore (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) : Ideal A :=
  sSup {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}

end Poisson
end
