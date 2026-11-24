module
public import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Theorem.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/
noncomputable section

namespace MetaMathlibExtTest

instance projZ : Projective Z :=
  hZeroObj.projective

end MetaMathlibExtTest
end
