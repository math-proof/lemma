import Lemma.AutomorphicForm.ArchWeightChar

set_option autoImplicit false

open MeasureTheory Polynomial

noncomputable section

namespace AutomorphicForm.GL2Real

def rotation (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
    (by rw [Matrix.det_fin_two_of]; nlinarith [Real.cos_sq_add_sin_sq θ])

def upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁, u; 0, a₂]
    (by rw [Matrix.det_fin_two_of]; simpa using h)

def upperHalfPlaneElt (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![y, x; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [hy.ne'])

def ellipticElt (r θ : ℝ) (hr : 0 < r) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ]
    (by
      rw [Matrix.det_fin_two_of]
      have h1 : 0 < r ^ 2 := by positivity
      nlinarith [Real.cos_sq_add_sin_sq θ])

def splitTransform (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ) : ℂ :=
  if h : a₁ * a₂ ≠ 0 then
    (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ,
        f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹)
  else 0

def ellipticTransform (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) : ℂ :=
  if hr : 0 < r then
    (4 * Real.sin θ ^ 2 : ℂ) *
      ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        if hy : 0 < y then
          (f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
              f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹)) /
            ((y : ℂ) ^ 2)
        else 0
  else 0

def discreteSeriesPairing (k : ℕ) (H : ℝ → ℝ → ℂ) (E : ℝ → ℝ → ℂ) (r : ℝ) : ℂ :=
  (∫ θ in (0 : ℝ)..Real.pi, E r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) -
    (2 * Real.pi / r : ℂ) *
      ∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
        (H (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ k * H (-(r * Real.exp t)) (-(r * Real.exp (-t))))

def entrySlice {P : Type*} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) : GL (Fin 2) ℝ → ℂ :=
  fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)

end AutomorphicForm.GL2Real

end
