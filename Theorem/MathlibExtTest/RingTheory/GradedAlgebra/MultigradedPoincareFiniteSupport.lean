/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

theorem hZeroObj : IsZero Z :=
  ModuleCat.isZero_of_subsingleton Z

end MetaMathlibExtTest
end
