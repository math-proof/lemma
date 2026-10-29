import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.RingTheory.GradedAlgebra.MultigradedPoincarePolynomial.Part7
open scoped DirectSum
open CategoryTheory CategoryTheory.Limits


namespace MetaMathlibExtTest

/--
[basisFinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean)
-/
@[path]
private lemma basisFinite (i : ℕ) : Finite (ι i) :=
  inferInstance

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[basisEmptyAbove](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean)
-/
@[path]
private lemma basisEmptyAbove (i : ℕ) (_ : 0 < i) : IsEmpty (ι i) :=
  inferInstance

end MetaMathlibExtTest

namespace MetaMathlibExtTest

/--
[poincareCoefficients_finiteSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedPoincarePolynomial.lean)
basis index type is empty, hence finite and empty above bound `0`. -/
@[path]
private theorem poincareCoefficients_finiteSupport :
  Function.HasFiniteSupport (MetaMathlibExt.multigradedPoincareCoefficients bc) :=
  MetaMathlibExt.multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution
    bc 0 basisFinite basisEmptyAbove

end MetaMathlibExtTest


-- created on 2026-10-23
-- updated on 2026-10-28
