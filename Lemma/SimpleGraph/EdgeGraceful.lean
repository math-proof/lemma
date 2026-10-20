import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.EdgeGraceful
open scoped BigOperators
open SimpleGraph


/--
[inducedResidue_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma inducedResidue_val_eq
  [Fintype V]
  {G : SimpleGraph V}
  {q : Nat}
  {v : V}
-- given
  (label : G.edgeSet ≃ Fin q)
  (hp : Fintype.card V ≠ 0) :
-- imply
  (G.inducedResidue q label v).val =
    G.incidentSum q label v % Fintype.card V := by
-- proof
  apply SimpleGraph.inducedResidue_val G q label v hp

/--
[isEdgeGraceful_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma isEdgeGraceful_iff_eq
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  G.IsEdgeGraceful ↔
    ∃ (q : Nat) (eLabel : G.edgeSet ≃ Fin q)
    (vLabel : V ≃ Fin (Fintype.card V)),
    ∀ v, vLabel v = G.inducedResidue q eLabel v ∧
    (Fintype.card V ≠ 0 →
    (vLabel v).val = G.incidentSum q eLabel v % Fintype.card V) := by
-- proof
  apply SimpleGraph.isEdgeGraceful_iff G


-- created on 2026-10-20
