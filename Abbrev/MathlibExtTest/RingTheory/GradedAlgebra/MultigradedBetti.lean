/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
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
