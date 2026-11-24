module
public import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Theorem.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
public import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/
noncomputable section

namespace MetaMathlibExtTest

theorem termSubsingleton (i : ℕ) :
    Subsingleton ↥(resolution.complex.X i) := by
  apply ModuleCat.isZero_iff_subsingleton.mp
  rw [resolution, ProjectiveResolution.self_complex]
  exact (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) i).map_isZero
    ((ChainComplex.single₀ (ModuleCat R)).map_isZero hZeroObj)

end MetaMathlibExtTest
end
