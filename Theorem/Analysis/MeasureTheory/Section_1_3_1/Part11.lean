import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part11


/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure, indicator) -/
lemma RealSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  RealSimpleFunction (E.indicator') := by
  use 1, fun _ => (1 : ℝ), fun _ => E
  constructor
  · intro
    exact hE
  · ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_one]
    simp

lemma ComplexSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  ComplexSimpleFunction (Complex.indicator E) := by
  use 1, fun _ => (1 : ℂ), fun _ => E
  constructor
  · intro
    exact hE
  · ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_one]
    simp [Complex.indicator, Real.complex_fun]

