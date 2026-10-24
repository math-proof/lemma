/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/LensCurvatureRecurrence.lean -/


import sympy.atlas.Geometry.LensCurvatureRecurrence

namespace MetaMathlibExt

example {b : ℕ → ℝ} {K A : ℝ} (h : IsLensCurvatureRecurrence b K A) : 1 + K ≠ 0 :=
  h.1

example {b : ℕ → ℝ} {K A : ℝ} (h : IsLensCurvatureRecurrence b K A) (n : ℕ) :
    b (n + 2) = ((6 - 2 * K) / (1 + K)) * b (n + 1) - b n + (-8 * A) / (1 + K) :=
  h.2 n

end MetaMathlibExt
