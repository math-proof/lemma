import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincareFiniteSupport.Part7
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


namespace MetaMathlibExtTest

/--
[basisFinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean)
-/
@[path]
private lemma basisFinite (i : ℕ) : Finite (ι i) :=
  inferInstance

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[basisEmptyAbove](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean)
-/
@[path]
private lemma basisEmptyAbove (i : ℕ) (_ : 0 < i) : IsEmpty (ι i) :=
  inferInstance

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[poincareCoefficients_finiteSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincareFiniteSupport.lean)
-/
@[path]
basis index type is empty, hence finite and empty above bound `0`. -/
private theorem poincareCoefficients_finiteSupport :
  Function.HasFiniteSupport (MetaMathlibExt.multigradedPoincareCoefficients bc) :=
  MetaMathlibExt.multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution
    bc 0 basisFinite basisEmptyAbove

end MetaMathlibExtTest


-- created on 2026-10-23
