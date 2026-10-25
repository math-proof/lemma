/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/FourierLaplace.lean -/


import sympy.atlas.Analysis.Fourier.FourierLaplace
open MeasureTheory


namespace FourierTest

noncomputable def compactlySupportedExample : ℝ → ℂ :=
  Set.Icc (-1 : ℝ) 1 |>.indicator fun _ => 1

end FourierTest
