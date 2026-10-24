/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MultipleBinomialTransform.lean -/


import sympy.atlas.Combinatorics.Enumerative.MultipleBinomialTransform

example (a : ℕ → ℤ) (n : ℕ) :
    MetaMathlibExt.multipleBinomialTransform 0 a n = a n :=
  rfl

example (a : ℕ → ℤ) (n : ℕ) :
    MetaMathlibExt.multipleBinomialTransform 1 a n =
      MetaMathlibExt.binomialTransform a n :=
  rfl

example :
    MetaMathlibExt.multipleBinomialTransform 2 (fun n => (n : ℤ)) 2 = 6 := by
  decide
