/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti.Part4
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

def compFn : (Fin n →₀ Int) →
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ) :=
  fun _ => (HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ))

end MetaMathlibExtTest
end
