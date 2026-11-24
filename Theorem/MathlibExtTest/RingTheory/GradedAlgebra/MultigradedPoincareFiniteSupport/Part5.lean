module
public import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Theorem.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport.Part3
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/
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
