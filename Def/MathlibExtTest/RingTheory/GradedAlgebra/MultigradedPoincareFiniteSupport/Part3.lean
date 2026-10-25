/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport.Part4
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
