module
public import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.Int.GradedAlgebra.MultigradedPoincarePolynomial
public import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/
noncomputable section

namespace MetaMathlibExtTest

theorem hZeroObj : IsZero Z :=
  ModuleCat.isZero_of_subsingleton Z

end MetaMathlibExtTest
end
