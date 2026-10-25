/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti.Part2
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

def trivialGrading {X : Type} [AddCommGroup X] [Module R X] [Module K X]
    [Subsingleton X] : MetaMathlibExt.MultigradedPolynomialModule K 0 X where
  component := fun _ => ⊥
  decomposition :=
    { decompose' := fun _ => 0
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun x => Subsingleton.elim _ _ }
  smul_via_C := fun k m => Subsingleton.elim _ _
  monomial_mem := by
    intro a c α m _
    change _ = 0
    exact Subsingleton.elim _ _

def targetGraded : MetaMathlibExt.MultigradedPolynomialModule K n M :=
  trivialGrading

end MetaMathlibExtTest
end
