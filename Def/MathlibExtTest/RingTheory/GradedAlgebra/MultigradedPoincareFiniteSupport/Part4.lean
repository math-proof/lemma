/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport.Part5
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

def inclFn (α : Fin n →₀ Int) :
    HomologicalComplex.Hom (compFn α)
      (MetaMathlibExt.baseChangedComplex resolution) where
  f := fun _ => 0
  comm' := by simp

end MetaMathlibExtTest
end
