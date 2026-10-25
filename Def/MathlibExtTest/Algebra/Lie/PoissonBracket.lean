/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/PoissonBracket.lean -/


import Theorem.Algebra.Lie.PoissonBracket


namespace MathlibExtTest.Algebra.Lie.PoissonBracket

open MathlibExt.Algebra.Lie.PoissonBracket

/-- The trivial (zero) Poisson bracket: every bracket vanishes. -/
def trivialBracket (A : Type) [CommRing A] [Algebra ℂ A] :
    PoissonBracket A where
  bracket := fun _ _ => 0
  add_left _ _ _ := by simp
  add_right _ _ _ := by simp
  skew _ _ := by simp
  leibniz _ _ _ := by simp
  jacobi _ _ _ := by simp
  smul_left _ _ _ := by simp
  smul_right _ _ _ := by simp

end MathlibExtTest.Algebra.Lie.PoissonBracket
