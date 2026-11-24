module
public import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Theorem.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Instance.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/
noncomputable section

namespace MetaMathlibExtTest

abbrev resolution : ProjectiveResolution Z :=
  ProjectiveResolution.self Z

abbrev ι : ℕ → Type := fun _ => Empty

end MetaMathlibExtTest
end
