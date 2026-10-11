import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Complex MeasureTheory Finset
open scoped Real

noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

/-!
# Multivariable logarithmic Mahler measure

For a Laurent polynomial in `n` variables, this file defines evaluation on the unit torus and the
normalized integral of the logarithm of its norm. This is the formula in arXiv:2608.01951v1,
`MMP5_arxiv_v1.tex`, lines 139–146.
-/

/-- The real phase `∑ j, e j * θ j` associated to an exponent vector `e`. -/
def realSum (θ : Fin n → ℝ) (e : Fin n → ℤ) : ℝ :=
  ∑ j, (e j : ℝ) * θ j

@[simp]
theorem realSum_zero (θ : Fin n → ℝ) : realSum θ 0 = 0 := by
  simp [realSum]

theorem realSum_add (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
    realSum θ (a + b) = realSum θ a + realSum θ b := by
  simp only [realSum, Pi.add_apply, Int.cast_add, add_mul, sum_add_distrib]

/-- The torus character `e ↦ exp (I * ∑ j, e j * θ j)` at the angle vector `θ`. -/
def torusCharacter (θ : Fin n → ℝ) (e : Fin n → ℤ) : ℂ :=
  Complex.exp (Complex.I * (realSum θ e : ℂ))

@[simp]
theorem torusCharacter_zero (θ : Fin n → ℝ) : torusCharacter θ 0 = 1 := by
  simp [torusCharacter]

theorem torusCharacter_add (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
    torusCharacter θ (a + b) = torusCharacter θ a * torusCharacter θ b := by
  simp only [torusCharacter, realSum_add, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- The multiplicative form of `torusCharacter`, used to evaluate a monoid algebra. -/
def torusCharacterHom (θ : Fin n → ℝ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun e := torusCharacter θ e.toAdd
  map_one' := by simp
  map_mul' a b := by
    have h : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    simpa only [h] using torusCharacter_add θ a.toAdd b.toAdd

/-- Evaluation of a multivariable Laurent polynomial at a point of the unit torus. -/
noncomputable def torusEval (θ : Fin n → ℝ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) →ₐ[ℂ] ℂ :=
  (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)) (torusCharacterHom θ)

@[simp]
theorem torusEval_single_zero (θ : Fin n → ℝ) (c : ℂ) :
    torusEval θ (AddMonoidAlgebra.single 0 c) = c := by
  simp [torusEval]

@[simp]
theorem torusEval_single (θ : Fin n → ℝ) (c : ℂ) (e : Fin n → ℤ) :
    torusEval θ (AddMonoidAlgebra.single e c) = c * torusCharacter θ e := by
  rw [torusEval, AddMonoidAlgebra.lift_single (torusCharacterHom θ) e c]
  simp [torusCharacterHom, smul_eq_mul]

/-- The normalized integral of `f` over the box `[0, 2π]ⁿ`. -/
noncomputable def normalizedBoxIntegral {m : ℕ} (f : (Fin m → ℝ) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ m)⁻¹ *
    ∫ x in Set.Icc (0 : Fin m → ℝ) (fun _ => 2 * Real.pi), f x ∂volume

/-- The multivariable logarithmic Mahler measure of a complex Laurent polynomial.

The cited source applies this formula to nonzero polynomials. Following Mathlib's
`Polynomial.logMahlerMeasure`, the Lean definition is total; in particular, its value at zero is
zero under `Real.log_zero` and the convention for the Bochner integral.
-/
noncomputable def logarithmicMahlerMeasure {m : ℕ}
    (F : AddMonoidAlgebra ℂ (Fin m → ℤ)) : ℝ :=
  normalizedBoxIntegral fun θ => Real.log ‖torusEval θ F‖

@[simp]
theorem logarithmicMahlerMeasure_const {m : ℕ} (c : ℂ) :
    logarithmicMahlerMeasure
      (AddMonoidAlgebra.single (0 : Fin m → ℤ) c) = Real.log ‖c‖ := by
  simp only [logarithmicMahlerMeasure, torusEval_single_zero, normalizedBoxIntegral,
    integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ, Measure.real]
  rw [Real.volume_Icc_pi_toReal (fun _ => by positivity)]
  simp [Finset.prod_const, Real.pi_ne_zero]

@[simp]
theorem logarithmicMahlerMeasure_zero {m : ℕ} :
    logarithmicMahlerMeasure (0 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
  simp [logarithmicMahlerMeasure, normalizedBoxIntegral]

/-- `Fin 1 → ℤ` is additively equivalent to `ℤ`. -/
def finOneAddEquiv : (Fin 1 → ℤ) ≃+ ℤ :=
  AddEquiv.funUnique (Fin 1) ℤ

/-- The one-variable multivariable-Laurent representation agrees with Mathlib's
`LaurentPolynomial ℂ = AddMonoidAlgebra ℂ ℤ`. -/
noncomputable def bridgeLaurent :
    AddMonoidAlgebra ℂ (Fin 1 → ℤ) ≃ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.domCongr ℂ ℂ finOneAddEquiv

@[simp]
theorem bridgeLaurent_single (c : ℂ) (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) c) =
      AddMonoidAlgebra.single k c := by
  simp [bridgeLaurent, finOneAddEquiv]

@[simp]
theorem bridgeLaurent_C (c : ℂ) :
    bridgeLaurent (AddMonoidAlgebra.single (0 : Fin 1 → ℤ) c) = LaurentPolynomial.C c := by
  rw [show (0 : Fin 1 → ℤ) = fun _ => 0 from rfl, bridgeLaurent_single]
  rfl

@[simp]
theorem bridgeLaurent_T (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) 1) = LaurentPolynomial.T k := by
  rw [bridgeLaurent_single]
  rfl

@[simp]
theorem logarithmicMahlerMeasure_one {m : ℕ} :
    logarithmicMahlerMeasure (1 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
  simp [logarithmicMahlerMeasure, normalizedBoxIntegral]

end MultivariableMahlerMeasure.MetaMathlibExt

end
