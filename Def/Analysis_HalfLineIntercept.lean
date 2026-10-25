import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

noncomputable section

namespace HalfLine

def slope (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F (R + 1) - F R)

def intercept (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F R - (R : ℂ) * slope F)


def affineExample (R : ℝ) : ℂ :=
  if R < 5 then 37 else (R : ℂ) * 3 + 7

end HalfLine

end
