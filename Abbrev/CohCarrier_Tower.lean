import Instance.CohCarrier_Level
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.Prod

set_option autoImplicit false

namespace CohCarrier

open Polynomial

section Linear

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

end Linear

section Leg

variable (R : Type*) [CommRing R]
variable {A : Type*} [AddCommGroup A] [Module R A] {B : Type*} [AddCommGroup B] [Module R B]
variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {M' : ℕ} {H' : Subgroup (ZMod M')ˣ}

end Leg

section Eisenstein

variable (R : Type*) [CommRing R] (A : Type*) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

noncomputable abbrev tw (ℓ₀ : ℕ) : R[X] := (X : R[X]) - C ((ℓ₀ : R) + 1)

end Eisenstein

section ThreeCopy

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable {L : Type*} [AddCommGroup L] [Module R L]
variable {L2 : Type*} [AddCommGroup L2] [Module R L2]

end ThreeCopy

end CohCarrier
