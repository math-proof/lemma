/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPolynomialModule.lean -/


import sympy.atlas.RingTheory.GradedAlgebra.MultigradedPolynomialModule


-- The zero exponent embeds as the zero grading index.
example {n : ℕ} : MetaMathlibExt.natDegreeToInt (0 : Fin n →₀ ℕ) = 0 := by
  simp [MetaMathlibExt.natDegreeToInt]

-- Embedded exponents add: shifting by `a + b` is shifting by `a` then `b`.
example {n : ℕ} (a b : Fin n →₀ ℕ) :
    MetaMathlibExt.natDegreeToInt (a + b) =
      MetaMathlibExt.natDegreeToInt a + MetaMathlibExt.natDegreeToInt b := by
  unfold MetaMathlibExt.natDegreeToInt
  ext i
  simp
