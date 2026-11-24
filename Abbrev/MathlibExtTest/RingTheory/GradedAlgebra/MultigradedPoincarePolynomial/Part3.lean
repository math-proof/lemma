module
public import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.Int.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part3
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/
noncomputable section

namespace MetaMathlibExtTest

abbrev decompAux (i : ℕ) : DirectSum.Decomposition
    (fun β => MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i β) := by
  have _hs := baseSubsingleton i
  refine { decompose' := fun _ => 0, left_inv := ?_, right_inv := ?_ } <;>
    intro x <;> exact Subsingleton.elim _ _

end MetaMathlibExtTest
end
