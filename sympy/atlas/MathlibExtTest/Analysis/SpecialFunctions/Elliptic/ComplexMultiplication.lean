/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/ComplexMultiplication.lean -/


import sympy.atlas.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication


namespace PeriodPair

variable (L : PeriodPair)

example : (0 : ℂ) ∈ L.endomorphismRing := by
  simp

example : (1 : ℂ) ∈ L.endomorphismRing := by
  simp

example : L.IsProperIdeal L.endomorphismRing := by
  simp

end PeriodPair
