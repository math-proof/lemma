import Mathlib
import Lemma.EllipticCurve.FrobeniusTrace
import Lemma.Matrix.MatrixRepresentationG.eq.MulVecLinValG
import Notation.ArtinL_EulerFactor

set_option autoImplicit false

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

theorem charpolyRev_eq_reverse_charpoly (T : W →ₗ[K] W) :
    charpolyRev T = (LinearMap.charpoly T).reverse := by
  rw [charpolyRev, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

theorem charpolyRev_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (T : W →ₗ[K] W) : (LinearMap.toMatrix b b T).charpolyRev = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

@[simp] theorem coeff_charpolyRev_zero (T : W →ₗ[K] W) : (charpolyRev T).coeff 0 = 1 := by
  rw [charpolyRev, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

@[simp] theorem coeff_charpolyRev_one (T : W →ₗ[K] W) :
    (charpolyRev T).coeff 1 = -LinearMap.trace K W T := by
  rw [charpolyRev, Matrix.coeff_charpolyRev_eq_neg_trace,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K W)]

theorem natDegree_charpolyRev_le (T : W →ₗ[K] W) :
    (charpolyRev T).natDegree ≤ Module.finrank K W := by
  rw [charpolyRev_eq_reverse_charpoly]
  exact (reverse_natDegree_le _).trans (LinearMap.charpoly_natDegree T).le

theorem charpolyRev_conj (e : W ≃ₗ[K] W') (T : W →ₗ[K] W) :
    charpolyRev (e.conj T) = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, charpolyRev_eq_reverse_charpoly, LinearEquiv.charpoly_conj]

theorem charpolyRev_ne_zero (T : W →ₗ[K] W) : charpolyRev T ≠ 0 := fun h => by
  simpa [h] using coeff_charpolyRev_zero T

theorem charpolyRev_mulVecLin {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    charpolyRev (Matrix.mulVecLin A) = A.charpolyRev := by
  rw [← charpolyRev_toMatrix (Pi.basisFun K (Fin m)), ← Matrix.toLin'_apply',
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem _root_.Matrix.charpolyRev_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    A.charpolyRev = 1 - C A.trace * X + C A.det * X ^ 2 := by
  rw [Matrix.charpolyRev, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [Matrix.smul_apply]
  ring

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

@[simp] theorem coeff_zero (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 0 = 0 := by
  simp [coeff]

@[simp] theorem coeff_one (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 1 = 1 := by
  simp [coeff]

@[simp] theorem coeff_eulerFactorAt_zero (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Γℚ) : (eulerFactorAt ρ A σ).coeff 0 = 1 := by
  unfold eulerFactorAt
  split_ifs <;> simp

@[simp] theorem coeff_eulerFactor_zero (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) :
    (eulerFactor ρ p).coeff 0 = 1 := by
  unfold eulerFactor
  split_ifs <;> simp

end ArtinL

end
