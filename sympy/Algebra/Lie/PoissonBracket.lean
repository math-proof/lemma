import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Bounds.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Prime

/-!
# Poisson brackets over commutative `ℂ`-algebras

Poisson-bracket interface over commutative `ℂ`-algebras: brackets,
Poisson ideals and primes, Poisson cores with their universal
property, and basic closure lemmas.
-/

noncomputable section

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

/-- Bracketing with zero vanishes. -/
theorem bracket_zero (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (a : A) : br.bracket a 0 = 0 := by
  have h := br.add_right a 0 0
  rw [add_zero] at h
  have h2 : br.bracket a 0 + 0 = br.bracket a 0 + br.bracket a 0 := by
    rw [add_zero]
    exact h
  have := add_left_cancel h2
  simpa using this.symm

/-- The zero ideal is Poisson. -/
theorem bot_poisson (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) : IsPoissonIdeal A br ⊥ := by
  intro a p hp
  rw [Submodule.mem_bot] at hp
  rw [hp, bracket_zero]
  exact Submodule.zero_mem _

/-- The supremum of two Poisson ideals below `J` is Poisson below `J`. -/
theorem sup_poisson {A : Type*} [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A)
    {J I K : Ideal A} (hI : I ≤ J ∧ IsPoissonIdeal A br I)
    (hK : K ≤ J ∧ IsPoissonIdeal A br K) :
    I ⊔ K ≤ J ∧ IsPoissonIdeal A br (I ⊔ K) := by
  refine ⟨sup_le hI.1 hK.1, fun a x hx => ?_⟩
  obtain ⟨i, hi, k, hk, rfl⟩ := Submodule.mem_sup.mp hx
  rw [br.add_right]
  exact add_mem (Ideal.mem_sup_left (hI.2 a i hi))
    (Ideal.mem_sup_right (hK.2 a k hk))

/-- The Poisson core of `J` is Poisson: the family of Poisson ideals
below `J` is directed (closed under suprema), so membership in the
core reduces to membership in some member. -/
theorem poissonCore_poisson (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsPoissonIdeal A br (poissonCore A br J) := by
  have hne : {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}.Nonempty :=
    ⟨⊥, bot_le, bot_poisson A br⟩
  have hdir : DirectedOn (· ≤ ·)
      {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P} := by
    intro I hI K hK
    exact ⟨I ⊔ K, sup_poisson br hI hK, le_sup_left, le_sup_right⟩
  have hmem {z : A} : z ∈ sSup {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P} ↔
      ∃ y ∈ {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}, z ∈ y :=
    Submodule.mem_sSup_of_directed hne hdir
  intro a p hp
  rw [poissonCore] at hp ⊢
  obtain ⟨I, hI, hpI⟩ := hmem.mp hp
  exact hmem.mpr ⟨I, hI, hI.2 a p hpI⟩

/-- The Poisson core lies below `J`. -/
theorem poissonCore_le (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    poissonCore A br J ≤ J :=
  sSup_le (fun P hP => hP.1)

/-- Every Poisson ideal below `J` lies below the core. -/
theorem le_poissonCore (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) {J P : Ideal A}
    (hP : P ≤ J ∧ IsPoissonIdeal A br P) :
    P ≤ poissonCore A br J :=
  le_sSup hP

/-- Universal property: the Poisson core is the largest Poisson ideal
below `J`. -/
theorem poissonCore_isGreatest (A : Type*) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsGreatest {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}
      (poissonCore A br J) :=
  ⟨⟨poissonCore_le A br J, poissonCore_poisson A br J⟩,
    fun P hP => le_poissonCore A br hP⟩

end Poisson
