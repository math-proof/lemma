module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Prime
public import Structure.Algebra.Lie.PoissonBracket

@[expose] public section

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
