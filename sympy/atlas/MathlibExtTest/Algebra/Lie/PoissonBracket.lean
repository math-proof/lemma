/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/PoissonBracket.lean -/


import sympy.atlas.Algebra.Lie.PoissonBracket


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

/-- The universal property is usable: the core is the greatest Poisson
ideal below `J`. -/
example (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsGreatest {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}
      (poissonCore A br J) :=
  poissonCore_isGreatest A br J

end MathlibExtTest.Algebra.Lie.PoissonBracket
