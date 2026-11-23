module

public import Mathlib
public import Theorem.WeierstrassCurve.FrobeniusTrace
public import Theorem.Matrix.MatrixRepresentationG.eq.MulVecLinValG
public import Notation.ArtinL_EulerFactor

public noncomputable section

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped MatrixGroups

namespace ArtinL


public theorem charpolyRev_eq_reverse_charpoly (T : W →ₗ[K] W) :
    charpolyRev T = (LinearMap.charpoly T).reverse := by
  rw [charpolyRev, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]


public theorem charpolyRev_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (T : W →ₗ[K] W) : (LinearMap.toMatrix b b T).charpolyRev = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]


@[simp] public theorem coeff_charpolyRev_zero (T : W →ₗ[K] W) : (charpolyRev T).coeff 0 = 1 := by
  rw [charpolyRev, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]


@[simp] public theorem coeff_charpolyRev_one (T : W →ₗ[K] W) :
    (charpolyRev T).coeff 1 = -LinearMap.trace K W T := by
  rw [charpolyRev, Matrix.coeff_charpolyRev_eq_neg_trace,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K W)]


public theorem natDegree_charpolyRev_le (T : W →ₗ[K] W) :
    (charpolyRev T).natDegree ≤ Module.finrank K W := by
  rw [charpolyRev_eq_reverse_charpoly]
  exact (reverse_natDegree_le _).trans (LinearMap.charpoly_natDegree T).le


public theorem charpolyRev_conj (e : W ≃ₗ[K] W') (T : W →ₗ[K] W) :
    charpolyRev (e.conj T) = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, charpolyRev_eq_reverse_charpoly, LinearEquiv.charpoly_conj]


public theorem charpolyRev_ne_zero (T : W →ₗ[K] W) : charpolyRev T ≠ 0 := fun h => by
  simpa [h] using coeff_charpolyRev_zero T


public theorem charpolyRev_mulVecLin {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    charpolyRev (Matrix.mulVecLin A) = A.charpolyRev := by
  rw [← charpolyRev_toMatrix (Pi.basisFun K (Fin m)), ← Matrix.toLin'_apply',
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']


public theorem _root_.Matrix.charpolyRev_fin_two (A : Matrix (Fin 2) (Fin 2) K) :
    A.charpolyRev = 1 - C A.trace * X + C A.det * X ^ 2 := by
  rw [Matrix.charpolyRev, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [Matrix.smul_apply]
  ring

end charpolyRev

variable {n : ℕ}

open scoped ArtinL_EulerFactor


@[simp] public theorem coeff_zero (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 0 = 0 := by
  simp [coeff]


@[simp] public theorem coeff_one (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 1 = 1 := by
  simp [coeff]


@[simp] public theorem coeff_eulerFactorAt_zero (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Γℚ) : (eulerFactorAt ρ A σ).coeff 0 = 1 := by
  unfold eulerFactorAt
  split_ifs <;> simp


@[simp] public theorem coeff_eulerFactor_zero (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) :
    (eulerFactor ρ p).coeff 0 = 1 := by
  unfold eulerFactor
  split_ifs <;> simp

end ArtinL

end
