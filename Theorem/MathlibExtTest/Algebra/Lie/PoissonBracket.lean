/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/PoissonBracket.lean -/


import Theorem.Algebra.Lie.PoissonBracket
import Def.MathlibExtTest.Algebra.Lie.PoissonBracket


namespace MathlibExtTest.Algebra.Lie.PoissonBracket

open MathlibExt.Algebra.Lie.PoissonBracket

/-- The universal property is usable: the core is the greatest Poisson
ideal below `J`. -/
example (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsGreatest {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}
      (poissonCore A br J) :=
  poissonCore_isGreatest A br J

end MathlibExtTest.Algebra.Lie.PoissonBracket
