module
public import Mathlib
public import Theorem.WeierstrassCurve.FrobeniusTrace
public import Def.Matrix_MatrixRepresentationG_eq_MulVecLinValG
public import Notation.ArtinL_EulerFactor
set_option autoImplicit false


public section

noncomputable section

open Polynomial
open scoped MatrixGroups

namespace ArtinL

def charpolyRev {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : W →ₗ[K] W) : K[X] :=
  (LinearMap.toMatrix (Module.finBasis K W) (Module.finBasis K W) T).charpolyRev

section charpolyRev

variable {K W W' : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']

end charpolyRev

variable {n : ℕ}

open scoped ArtinL_EulerFactor

def invariantsUnder (ρ : Γℚ →* GL (Fin n) ℂ) (H : Subgroup Γℚ) : Submodule ℂ (Fin n → ℂ) :=
  Representation.invariants ((Deformation.matrixRepresentation ρ).comp H.subtype)

abbrev inertiaInvariants (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) : Submodule ℂ (Fin n → ℂ) :=
  invariantsUnder ρ (A.inertiaSubgroupIn ℚ)

open scoped Classical in

def eulerFactorAt (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : Γℚ) : ℂ[X] :=
  if h : ∀ v ∈ inertiaInvariants ρ A,
      Deformation.matrixRepresentation ρ σ v ∈ inertiaInvariants ρ A then
    charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict h)
  else 1

open scoped Classical in

def eulerFactor (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ℂ[X] :=
  if h : ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∃ σ : Γℚ,
      A.LiesOverPrime p ∧ A.IsFrobeniusAt σ p then
    eulerFactorAt ρ h.choose h.choose_spec.choose
  else 1

def coeffPrimePow (ρ : Γℚ →* GL (Fin n) ℂ) (p k : ℕ) : ℂ :=
  PowerSeries.coeff k ((eulerFactor ρ p : PowerSeries ℂ)⁻¹)

def coeff (ρ : Γℚ →* GL (Fin n) ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else m.factorization.prod fun p k => coeffPrimePow ρ p k

def LSeries (ρ : Γℚ →* GL (Fin n) ℂ) (s : ℂ) : ℂ :=
  _root_.LSeries (coeff ρ) s

end ArtinL

end
