import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv

set_option autoImplicit false

noncomputable section

open MeasureTheory Real

namespace MvPolynomial

variable {n : ℕ}

def torusBox (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ : Fin n ↦ Set.Ioc 0 (2 * π)


def logMahlerMeasure (P : MvPolynomial (Fin n) ℂ) : ℝ :=
  ((2 * π)⁻¹) ^ n * ∫ θ in torusBox n, Real.log ‖eval (fun i ↦ circleMap 0 1 (θ i)) P‖

end MvPolynomial

end
