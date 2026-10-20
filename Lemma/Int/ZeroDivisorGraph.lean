import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.ZeroDivisorGraph
open ZeroDivisorGraph


/--
[exists_vertex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ZeroDivisorGraph.lean)
-/
@[path]
private lemma exists_vertex_iff_eq
  {R : Type u} [CommRing R]
  {r : R} :
-- imply
  (∃ v : Vertex R, (v : R) = r) ↔ (r ≠ 0 ∧ r ∉ nonZeroDivisors R) := by
-- proof
  apply ZeroDivisorGraph.exists_vertex_iff R r

/--
[adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ZeroDivisorGraph.lean)
-/
@[path]
private lemma adj_iff_eq
  {R : Type u} [CommRing R]
  {v w : Vertex R} :
-- imply
  (zeroDivisorGraph R).Adj v w ↔ v ≠ w ∧ (v : R) * (w : R) = 0 := by
-- proof
  apply ZeroDivisorGraph.adj_iff R


-- created on 2026-10-20
