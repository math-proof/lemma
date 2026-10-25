/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
import Lemma.Int.GradedAlgebra.MultigradedPoincarePolynomial
import Instance.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

abbrev resolution : ProjectiveResolution Z :=
  ProjectiveResolution.self Z

abbrev ι : ℕ → Type := fun _ => Empty

end MetaMathlibExtTest
end
