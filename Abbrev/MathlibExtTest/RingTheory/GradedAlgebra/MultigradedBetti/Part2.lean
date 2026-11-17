/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/


module

public import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
public import Instance.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


@[expose] public noncomputable section

namespace MetaMathlibExtTest

abbrev resolution : ProjectiveResolution Z :=
  ProjectiveResolution.self Z

abbrev ι : ℕ → Type := fun _ => Empty

end MetaMathlibExtTest
end
