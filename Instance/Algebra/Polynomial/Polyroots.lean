import Theorem.Algebra.Power.Part2
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Hyperreal
import Notation.Algebra.Polynomial.Polyroots


noncomputable instance : Root ℝ where
  sqrt := Real.sqrt
  cubic x := x ^ (3:ℝ)⁻¹
  quartic x := x ^ (4:ℝ)⁻¹

noncomputable instance : Pow ℝ* ℝ* where
  pow x y := x.map₂ Real.rpow y

noncomputable instance : Root ℝ* where
  sqrt x := x.map Real.sqrt
  cubic x := x ^ (3:ℝ*)⁻¹
  quartic x := x ^ (4:ℝ*)⁻¹


noncomputable instance : Root ℂ where
  sqrt x := x ^ (2:ℂ)⁻¹
  cubic x := x ^ (3:ℂ)⁻¹
  quartic x := x ^ (4:ℂ)⁻¹

