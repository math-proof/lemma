import Mathlib
import sympy.Basic
import Instance.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part3


/--
[derivative_antideriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean)
-/
@[path]
private lemma derivative_antideriv_eq
  {g : Polynomial ℝ} :
-- imply
  Polynomial.derivative (polyAntideriv g) = g := by
-- proof
  apply derivative_antideriv g

/--
[polyOmega_zero_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean)
-/
@[path]
private lemma polyOmega_zero_nontrivial_eq :
-- imply
  (0 : PolyΩ 0) ≠ (1 : PolyΩ 0) := by
-- proof
  apply polyOmega_zero_nontrivial

/--
[polyOmega_one_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean)
-/
@[path]
private lemma polyOmega_one_nontrivial_eq :
-- imply
  (0 : PolyΩ 1) ≠ (1 : PolyΩ 1) := by
-- proof
  apply polyOmega_one_nontrivial


-- created on 2026-10-23
