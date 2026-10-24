/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/FastFourierTransform.lean -/


import sympy.atlas.Analysis.Fourier.FastFourierTransform
import Mathlib.Tactic.NormNum

namespace MathlibExt.Analysis.Fourier.FastFourierTransformWanted

-- The recurrence lifts a known size-two cost to size four.
example (h : fftCost 2 = 2) : fftCost 4 = 8 := by
  calc
    fftCost 4 = 2 * fftCost 2 + 2 * 2 := by
      simpa using fftCost_recurrence 2 (by norm_num)
    _ = 8 := by norm_num [h]

-- Concrete two-point transforms exercise periodicity and both splitting forms.
example :
    dftSum 2 (-1) (fun j => ((j + 1 : ℕ) : ℂ)) 3 = -1 ∧
      dftSum 2 2 (fun j => ((j + 1 : ℕ) : ℂ)) 1 = 5 := by
  constructor
  · calc
      dftSum 2 (-1) (fun j => ((j + 1 : ℕ) : ℂ)) 3 =
          dftSum 2 (-1) (fun j => ((j + 1 : ℕ) : ℂ)) (3 % 2) := by
        exact dftSum_mod 2 (-1) (by norm_num) (fun j => ((j + 1 : ℕ) : ℂ)) 3
      _ = -1 := by
        rw [cooley_tukey 1 (-1) (by norm_num)]
        norm_num [dftSum]
  · rw [dftSum_two_mul 1 2]
    norm_num [dftSum]

end MathlibExt.Analysis.Fourier.FastFourierTransformWanted
