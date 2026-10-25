/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

instance projZ : Projective Z :=
  hZeroObj.projective

end MetaMathlibExtTest
end
