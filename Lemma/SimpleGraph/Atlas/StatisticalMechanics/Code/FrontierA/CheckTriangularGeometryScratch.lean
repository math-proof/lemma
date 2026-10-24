import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.CheckTriangularGeometryScratch
open StatMech StatMech.FrontierA


/--
[triangular_edge_eq_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckTriangularGeometryScratch.lean)
-/
@[path]
private lemma triangular_edge_eq_canonical_eq
  {p : Int × Int}
  {a : Fin 6} :
-- imply
  s(p, p + triangularIntStep a) = s(triangularCanonicalBase p a, triangularCanonicalBase p a + triangularCanonicalStep (triangularCanonicalKind a)) := by
-- proof
  apply StatMech.FrontierA.triangular_edge_eq_canonical p a

/--
[triangular_sbtw_canonical_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckTriangularGeometryScratch.lean)
-/
@[path]
private lemma triangular_sbtw_canonical_iff_eq
  {p : Int × Int}
  {a : Fin 6}
  {z : Complex} :
-- imply
  Sbtw Real (triangularIntPoint p) z (triangularIntPoint (p + triangularIntStep a)) ↔ Sbtw Real (triangularIntPoint (triangularCanonicalBase p a)) z (triangularIntPoint (triangularCanonicalBase p a + triangularCanonicalStep (triangularCanonicalKind a))) := by
-- proof
  apply StatMech.FrontierA.triangular_sbtw_canonical_iff p a z

/--
[scratch_open_intersection_edge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckTriangularGeometryScratch.lean)
-/
@[path]
private lemma scratch_open_intersection_edge_eq_eq
  {p q : Int × Int}
  {a b : Fin 6}
  {z : Complex}
-- given
  (hp : Sbtw Real (triangularIntPoint p) z (triangularIntPoint (p + triangularIntStep a)))
  (hq : Sbtw Real (triangularIntPoint q) z (triangularIntPoint (q + triangularIntStep b))) :
-- imply
  s(p, p + triangularIntStep a) = s(q, q + triangularIntStep b) := by
-- proof
  apply StatMech.FrontierA.scratch_open_intersection_edge_eq p q a b z hp hq


-- created on 2026-10-23
