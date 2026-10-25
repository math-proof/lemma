/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBetti.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
import Abbrev.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedBetti.Part3
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

theorem diffPresAux : ∀ (i : ℕ) (β : Fin n →₀ Int)
    (x : ↥((MetaMathlibExt.baseChangedComplex resolution).X (i + 1))),
    x ∈ MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree (i + 1) β →
    ModuleCat.Hom.hom ((MetaMathlibExt.baseChangedComplex resolution).d (i + 1) i) x ∈
      MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i β := by
  intro i β x _
  rw [pieceIsBot i β]
  have _hs := baseSubsingleton i
  change _ = 0
  exact Subsingleton.elim _ _

end MetaMathlibExtTest
end
