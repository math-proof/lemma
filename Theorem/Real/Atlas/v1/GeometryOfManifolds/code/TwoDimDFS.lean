module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part3


public section

/--
[pderiv_comm_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean)
-/
@[path]
private theorem pderiv_comm_poly_eq
  {i j : Fin 2}
  {f : Poly2} :
-- imply
  MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
-- proof
  apply pderiv_comm_poly i j f


-- created on 2026-10-23
