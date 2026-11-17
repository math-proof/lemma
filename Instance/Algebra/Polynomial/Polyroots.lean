module

public import Theorem.Algebra.Power.Part2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Hyperreal
public import Notation.Algebra.Polynomial.Polyroots

@[expose] public section

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

