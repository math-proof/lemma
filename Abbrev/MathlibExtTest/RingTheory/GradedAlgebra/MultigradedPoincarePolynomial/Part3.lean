/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
import Lemma.Int.GradedAlgebra.MultigradedPoincarePolynomial
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part3
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

abbrev decompAux (i : ℕ) : DirectSum.Decomposition
    (fun β => MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i β) := by
  have _hs := baseSubsingleton i
  refine { decompose' := fun _ => 0, left_inv := ?_, right_inv := ?_ } <;>
    intro x <;> exact Subsingleton.elim _ _

end MetaMathlibExtTest
end
