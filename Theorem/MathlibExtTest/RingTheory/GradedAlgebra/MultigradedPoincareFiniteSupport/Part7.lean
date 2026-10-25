/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean -/


import Theorem.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport
import Lemma.Int.GradedAlgebra.MultigradedPoincareFiniteSupport
import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport.Part5
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

theorem componentHomologyIsZero (alpha : Fin n →₀ Int) (i : ℕ)
    [HomologicalComplex.HasHomology (bc.comp alpha) i] :
    IsZero (HomologicalComplex.homology (bc.comp alpha) i) := by
  apply ((bc.comp alpha).sc i).isZero_homology_of_isZero_X₂
  change IsZero ((HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ)).X i)
  exact compTermIsZero i

theorem betti_at_zero_is_zero :
    MetaMathlibExt.multigradedBettiNumber bc 0 0 = 0 := by
  have _hHom := bc.hasHom 0 0
  have _hFinite := bc.finiteDim 0 0
  change Module.finrank K ↥(HomologicalComplex.homology (bc.comp 0) 0) = 0
  have _hs : Subsingleton ↥(HomologicalComplex.homology (bc.comp 0) 0) :=
    ModuleCat.isZero_iff_subsingleton.mp (componentHomologyIsZero 0 0)
  exact Module.finrank_zero_of_subsingleton

end MetaMathlibExtTest
end
