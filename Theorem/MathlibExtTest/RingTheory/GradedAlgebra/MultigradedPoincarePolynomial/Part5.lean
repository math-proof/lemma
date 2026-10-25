/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
import Lemma.Int.GradedAlgebra.MultigradedPoincarePolynomial
import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part3
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

theorem compTermIsZero (i : ℕ) :
    IsZero ((HomologicalComplex.zero :
      HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ)).X i) :=
  isZero_zero _

theorem compTermSubsingleton (α : Fin n →₀ Int) (i : ℕ) :
    Subsingleton ↥((compFn α).X i) :=
  ModuleCat.isZero_iff_subsingleton.mp (compTermIsZero i)

end MetaMathlibExtTest
end
