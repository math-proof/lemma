/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/

module

public import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
public import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti

@[expose] public section

open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

instance projZ : Projective Z :=
  hZeroObj.projective

end MetaMathlibExtTest
end
