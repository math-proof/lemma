import Def.TateCurve_PointSeries
import Def.TateCurve_Tails
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

section CauchyProduct

variable {K : Type*} [NontriviallyNormedField K] {q : K}

noncomputable def cauchyMul (c d : ℕ → K) (N : ℕ) : K :=
  ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal N, c kl.1 * d kl.2

end CauchyProduct

section Coefficients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

noncomputable def xCoeffFull (u : K) : ℕ → K
  | 0 => xfun u
  | (N + 1) => xCoeff u (N + 1)


noncomputable def yCoeffFull (u : K) : ℕ → K
  | 0 => yfun u
  | (N + 1) => yCoeff u (N + 1)


noncomputable def a₄Coeff : ℕ → K
  | 0 => 0
  | (N + 1) => -(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K))


noncomputable def a₆Coeff : ℕ → K
  | 0 => 0
  | (N + 1) => -(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K))


noncomputable def seriesBound (u : K) : ℝ := max (max ‖xfun u‖ ‖yfun u‖) 1

end Coefficients

section Defect

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

noncomputable def defectCoeff (u : K) (N : ℕ) : K :=
  cauchyMul (yCoeffFull u) (yCoeffFull u) N + cauchyMul (xCoeffFull u) (yCoeffFull u) N
    - (cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
        + cauchyMul a₄Coeff (xCoeffFull u) N + a₆Coeff N)

end Defect

end TateCurve
