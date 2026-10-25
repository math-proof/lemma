/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

abbrev K : Type := Rat

abbrev n : ℕ := 0

abbrev R : Type := MvPolynomial (Fin n) K

abbrev M : Type := PUnit

abbrev Z : ModuleCat R := ModuleCat.of R M

end MetaMathlibExtTest
end
