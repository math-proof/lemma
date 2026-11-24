module
public import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Theorem.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/
noncomputable section

namespace MetaMathlibExtTest

theorem hZeroObj : IsZero Z :=
  ModuleCat.isZero_of_subsingleton Z

end MetaMathlibExtTest
end
