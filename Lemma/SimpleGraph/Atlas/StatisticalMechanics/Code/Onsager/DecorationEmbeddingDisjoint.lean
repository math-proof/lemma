import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
open StatMech StatMech.Onsager


/--
[ons_decEmbedWalk_support_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingDisjoint.lean)
-/
@[path]
private lemma ons_decEmbedWalk_support_disjoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v x y : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {r : (ons_decGraph L).Walk x y}
-- given
  (hdisj : List.Disjoint p.support r.support) :
-- imply
  List.Disjoint (ons_decEmbedWalk L p).support (ons_decEmbedWalk L r).support := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_support_disjoint L p r hdisj

/--
[ons_decEmbedWalk_support_disjoint_of_toSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingDisjoint.lean)
-/
@[path]
private lemma ons_decEmbedWalk_support_disjoint_of_toSubgraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {u v x y : ons_Dart L}
  {p : (ons_decGraph L).Walk u v}
  {r : (ons_decGraph L).Walk x y}
-- given
  (hdisj : Disjoint p.toSubgraph.verts r.toSubgraph.verts) :
-- imply
  List.Disjoint (ons_decEmbedWalk L p).support (ons_decEmbedWalk L r).support := by
-- proof
  apply StatMech.Onsager.ons_decEmbedWalk_support_disjoint_of_toSubgraph L p r hdisj


-- created on 2026-10-23
