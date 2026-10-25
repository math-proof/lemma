/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean -/


import Def.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial
import Lemma.Int.GradedAlgebra.MultigradedPoincarePolynomial
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part2
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


noncomputable section

namespace MetaMathlibExtTest

def termFreeModule (i : ℕ) :
    letI : Module K ↥(resolution.complex.X i) :=
      Module.compHom _ (MvPolynomial.C : K →+* R);
    MetaMathlibExt.MultigradedFreeModule K n ↥(resolution.complex.X i) (ι i) := by
  haveI := termSubsingleton i
  letI : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* R)
  exact
    { graded := trivialGrading
      basis := Module.Basis.empty _
      degree := fun j => j.elim
      basis_mem := fun j => j.elim }

def resFree :
    MetaMathlibExt.MultigradedFreeResolution K n M targetGraded resolution ι where
  termFree := fun i => termFreeModule i
  diffDegreeZero := by
    intro i alpha m hm
    have _hNext : Subsingleton ↥(resolution.complex.X (i + 1)) :=
      termSubsingleton (i + 1)
    have _hCurr : Subsingleton ↥(resolution.complex.X i) := termSubsingleton i
    change _ = 0
    exact Subsingleton.elim _ _
  augDegreeZero := by
    intro alpha m hm
    have _hTerm : Subsingleton ↥(resolution.complex.X 0) := termSubsingleton 0
    change _ = 0
    exact Subsingleton.elim _ _

end MetaMathlibExtTest
end
