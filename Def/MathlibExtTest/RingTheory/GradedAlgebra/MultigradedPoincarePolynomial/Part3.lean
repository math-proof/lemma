module
public import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.Int.GradedAlgebra.MultigradedPoincarePolynomial
public import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part4
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/
noncomputable section

namespace MetaMathlibExtTest

def compFn : (Fin n →₀ Int) →
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ) :=
  fun _ => (HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ))

end MetaMathlibExtTest
end
