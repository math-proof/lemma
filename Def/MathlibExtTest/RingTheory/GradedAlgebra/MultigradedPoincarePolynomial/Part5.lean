/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
import Lemma.Int.GradedAlgebra.MultigradedPoincarePolynomial
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part6
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

def bc : MetaMathlibExt.MultigradedBaseChange
    targetGraded resolution ι resFree where
  decomposition := fun i => decompAux i
  diffPreserves := fun i β x hx => diffPresAux i β x hx
  comp := fun _ => (HomologicalComplex.zero :
    HomologicalComplex (ModuleCat K) (ComplexShape.down ℕ))
  incl := fun α => inclFn α
  incl_injective := fun α i => inclInjAux α i
  range_eq := fun α i => rangeEqAux α i
  hasHom := by
    intro alpha i
    exact ShortComplex.hasHomology_of_zeros _ _ _
  finiteDim := by
    intro alpha i _
    have hH : IsZero (HomologicalComplex.homology
        (HomologicalComplex.zero : HomologicalComplex (ModuleCat K)
          (ComplexShape.down ℕ)) i) :=
      ((HomologicalComplex.zero : HomologicalComplex (ModuleCat K)
        (ComplexShape.down ℕ)).sc i).isZero_homology_of_isZero_X₂
        (compTermIsZero i)
    have hSub : Subsingleton ↥(HomologicalComplex.homology
        (HomologicalComplex.zero : HomologicalComplex (ModuleCat K)
          (ComplexShape.down ℕ)) i) :=
      ModuleCat.isZero_iff_subsingleton.mp hH
    have _hFin := hSub
    exact Module.Finite.of_basis (Module.Basis.empty (ι := Empty) _)

end MetaMathlibExtTest
end
