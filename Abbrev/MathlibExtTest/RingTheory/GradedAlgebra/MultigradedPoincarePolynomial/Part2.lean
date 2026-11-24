module
public import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.Int.GradedAlgebra.MultigradedPoincarePolynomial
public import Instance.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/
noncomputable section

namespace MetaMathlibExtTest

abbrev resolution : ProjectiveResolution Z :=
  ProjectiveResolution.self Z

abbrev ι : ℕ → Type := fun _ => Empty

end MetaMathlibExtTest
end
