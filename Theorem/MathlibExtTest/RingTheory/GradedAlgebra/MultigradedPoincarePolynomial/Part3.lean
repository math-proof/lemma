/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
import Lemma.Int.GradedAlgebra.MultigradedPoincarePolynomial
import Def.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part2
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

theorem baseZero (i : ℕ) :
    IsZero ((MetaMathlibExt.baseChangedComplex resolution).X i) := by
  let _alg : Algebra R K := MetaMathlibExt.zeroEval.toAlgebra
  have hSingle : IsZero ((ChainComplex.single₀ (ModuleCat R)).obj Z) :=
    (ChainComplex.single₀ (ModuleCat R)).map_isZero hZeroObj
  have hRes : IsZero resolution.complex := by
    simp only [resolution, ProjectiveResolution.self_complex]
    exact hSingle
  have hMap : IsZero
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars MetaMathlibExt.zeroEval)
        (ComplexShape.down ℕ)).obj resolution.complex) :=
    Functor.map_isZero _ hRes
  have hEval : IsZero
      (((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars MetaMathlibExt.zeroEval)
        (ComplexShape.down ℕ)).obj resolution.complex).X i) :=
    Functor.map_isZero
      (HomologicalComplex.eval (ModuleCat K) (ComplexShape.down ℕ) i) hMap
  exact hEval

theorem baseSubsingleton (i : ℕ) :
    Subsingleton ↥((MetaMathlibExt.baseChangedComplex resolution).X i) :=
  ModuleCat.isZero_iff_subsingleton.mp (baseZero i)

theorem pieceIsBot (i : ℕ) (α : Fin n →₀ Int) :
    MetaMathlibExt.baseChangedDegreePiece targetGraded resolution ι resFree i α
      = ⊥ := by
  have _hs := baseSubsingleton i
  apply le_antisymm
  · intro y _
    have hy0 : y = 0 := Subsingleton.elim _ _
    rw [hy0]
    exact Submodule.zero_mem _
  · exact bot_le

end MetaMathlibExtTest
end
