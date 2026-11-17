/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/
module

public import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
public import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits

public section

noncomputable section

namespace MetaMathlibExtTest

theorem hZeroObj : IsZero Z :=
  ModuleCat.isZero_of_subsingleton Z

end MetaMathlibExtTest
end
