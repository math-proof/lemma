/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Entry16PsiSeries.lean -/


import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry16PsiSeries
import Lemma.Nat.Ramanujan.Part1Ch3Entry16PsiSeries

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16PsiSeries

-- The public identity specializes to the Jensen-series base case at `r = 0`.
example (n u : ℂ) (h : ‖u * Complex.exp (1 - u)‖ < 1) (hu : ‖u‖ < 1) :
    HasSum (fun j : ℕ =>
      (n + (j : ℂ)) ^ j * Complex.exp (-u * (n + (j : ℂ))) * u ^ j /
        (Nat.factorial j : ℂ)) (1 / (1 - u)) := by
  simpa [psi] using ramanujan_part1_ch3_entry16_psi_series 0 n u h hu

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16PsiSeries
