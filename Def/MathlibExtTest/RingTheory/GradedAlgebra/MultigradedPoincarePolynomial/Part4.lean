module
public import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.Int.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part5
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/
noncomputable section

namespace MetaMathlibExtTest

def inclFn (α : Fin n →₀ Int) :
    HomologicalComplex.Hom (compFn α)
      (MetaMathlibExt.baseChangedComplex resolution) where
  f := fun _ => 0
  comm' := by simp

end MetaMathlibExtTest
end
