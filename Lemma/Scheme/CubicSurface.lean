import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.CubicSurface

open AlgebraicGeometry
open MvPolynomial

/--
[totalDegree_defining](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/CubicSurface.lean)
-/
@[path]
private lemma totalDegree_defining_eq
  [Field k]
-- given
  (S : CubicSurface k) :
-- imply
  S.defining.totalDegree = 3 := by
-- proof
  apply CubicSurface.totalDegree_defining


/--
[isHomogeneous_pderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/CubicSurface.lean)
-/
@[path]
private lemma isHomogeneous_pderiv_eq
  [Field k]
-- given
  (S : CubicSurface k) (i : Fin 4) :
-- imply
  (pderiv i S.defining).IsHomogeneous 2 := by
-- proof
  apply CubicSurface.isHomogeneous_pderiv


/--
[aeval_defining_eq_zero_of_pderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/CubicSurface.lean)
-/
@[path]
private lemma aeval_defining_eq_zero_of_pderiv_eq
  [Field k]
-- given
  (S : CubicSurface k) (h3 : (3 : k) ≠ 0) {x : Fin 4 → k}
  (hx : ∀ i, aeval x (pderiv i S.defining) = 0) :
-- imply
  aeval x S.defining = 0 := by
-- proof
  apply CubicSurface.aeval_defining_eq_zero_of_pderiv
  · exact h3
  · exact hx


/--
[isSingularPoint_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/CubicSurface.lean)
-/
@[path]
private lemma isSingularPoint_iff_eq
  [Field k]
-- given
  (h3 : (3 : k) ≠ 0) (S : CubicSurface k) (x : Fin 4 → k) :
-- imply
  S.IsSingularPoint x ↔ ∀ i, aeval x (pderiv i S.defining) = 0 := by
-- proof
  apply CubicSurface.isSingularPoint_iff
  · exact h3


-- created on 2026-10-09
