import Mathlib
import sympy.Basic
open MvPolynomial


noncomputable def wCubic {F : Type*} [CommRing F] (V : WeierstrassCurve.Projective F) : Cubic (MvPolynomial (Fin 2) F) :=
  ⟨1, C V.a₂ * X 1, C V.a₄ * X 1 ^ 2 - C V.a₁ * X 0 * X 1,
    C V.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1 - C V.a₃ * X 0 * X 1 ^ 2⟩


/--
[wCubic_toPoly_coeff_zero]
-/
@[path]
private lemma main
-- given
  {F : Type*}
  [CommRing F]
  (V : WeierstrassCurve.Projective F) :
-- imply
  (wCubic V).toPoly.coeff 0 =
    C V.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1 - C V.a₃ * X 0 * X 1 ^ 2 := by
-- proof
  rw [Cubic.coeff_eq_d]
  rfl


-- created on 2026-10-24
