import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
open StatMech StatMech.FrontierA


/--
[triangularTorusSplitOffset_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitOffset_injective_eq :
-- imply
  Function.Injective triangularTorusSplitOffset := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitOffset_injective

/--
[triangularTorusSplitOffset_fst_lt_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitOffset_fst_lt_three_eq
  {a : Fin 6} :
-- imply
  (triangularTorusSplitOffset a).1 < 3 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitOffset_fst_lt_three a

/--
[triangularTorusSplitOffset_snd_lt_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitOffset_snd_lt_three_eq
  {a : Fin 6} :
-- imply
  (triangularTorusSplitOffset a).2 < 3 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitOffset_snd_lt_three a

/--
[triangularTorusSplitEmbedCoord_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedCoord_lt_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L}
  {c : Nat}
-- given
  (hc : c < 3) :
-- imply
  3 * z.val + c < 3 * L := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedCoord_lt L z c hc

/--
[triangularTorusSplitEmbedVertex_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_fst_val_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  (triangularTorusSplitEmbedVertex L p).1.val = 3 * p.1.1.val + (triangularTorusSplitOffset (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_fst_val L p

/--
[triangularTorusSplitEmbedVertex_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_snd_val_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  (triangularTorusSplitEmbedVertex L p).2.val = 3 * p.1.2.val + (triangularTorusSplitOffset (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_snd_val L p

/--
[triangularTorusGraphDartDirection_fst_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusGraphDartDirection_fst_injective_eq
  {L : Nat}
  [Fact (2 < L)]
  {d e : (triangularTorusGraph L).Dart}
-- given
  (hfst : d.fst = e.fst)
  (hdir : triangularTorusGraphDartDirection L d = triangularTorusGraphDartDirection L e) :
-- imply
  d = e := by
-- proof
  apply StatMech.FrontierA.triangularTorusGraphDartDirection_fst_injective L hfst hdir

/--
[triangularTorusSplitEmbedVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_injective_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  Function.Injective (triangularTorusSplitEmbedVertex L) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_injective L

/--
[triangular_three_zmodCast_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangular_three_zmodCast_add_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (3 : ZMod (3 * L)) * ZMod.cast z + 3 = 3 * ZMod.cast (z + 1) := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_add_one L z

/--
[triangular_three_zmodCast_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangular_three_zmodCast_sub_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (3 : ZMod (3 * L)) * ZMod.cast z - 3 = 3 * ZMod.cast (z - 1) := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_sub_one L z

/--
[triangular_three_zmodCast_add_one_rearranged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangular_three_zmodCast_add_one_rearranged_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (ZMod.cast (1 + z) : ZMod (3 * L)) * 3 = 3 + ZMod.cast z * 3 := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_add_one_rearranged L z

/--
[triangular_three_zmodCast_sub_one_rearranged](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangular_three_zmodCast_sub_one_rearranged_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  2 + (ZMod.cast (-1 + z) : ZMod (3 * L)) * 3 = -1 + ZMod.cast z * 3 := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_sub_one_rearranged L z

/--
[triangularTorusSplitEmbedVertex_eq_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_eq_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  triangularTorusSplitEmbedVertex L p = ((3 : ZMod (3 * L)) * ZMod.cast p.1.1 + (triangularTorusSplitOffset (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).1, (3 : ZMod (3 * L)) * ZMod.cast p.1.2 + (triangularTorusSplitOffset (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).2) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_eq_cast L p

/--
[triangularTorusDirectionStep_add_intStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusDirectionStep_add_intStep_eq
  {L : Nat}
  {a : Fin 6} :
-- imply
  triangularTorusDirectionStep L a + (((triangularIntStep a).1 : ZMod L), ((triangularIntStep a).2 : ZMod L)) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionStep_add_intStep L a

/--
[triangularTorusGraphDartDirection_dartEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusGraphDartDirection_dartEquiv_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : triangularTorusDart L} :
-- imply
  triangularTorusGraphDartDirection L (triangularTorusDartEquiv L a) = a.2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusGraphDartDirection_dartEquiv L a

/--
[triangularTorusGraphDart_snd_eq_fst_add_intStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusGraphDart_snd_eq_fst_add_intStep_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (triangularTorusGraph L).Dart} :
-- imply
  d.snd = d.fst + (((triangularIntStep (triangularTorusGraphDartDirection L d)).1 : ZMod L), ((triangularIntStep (triangularTorusGraphDartDirection L d)).2 : ZMod L)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusGraphDart_snd_eq_fst_add_intStep L d

/--
[triangularTorusAdj_add_intStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusAdj_add_intStep_eq
  {N : Nat}
  [Fact (2 < N)]
  {z : ZMod N × ZMod N}
  {a : Fin 6} :
-- imply
  (triangularTorusGraph N).Adj z (z + (((triangularIntStep a).1 : ZMod N), ((triangularIntStep a).2 : ZMod N))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusAdj_add_intStep N z a

/--
[triangularTorusSplitOffset_adj_of_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitOffset_adj_of_rank_eq
  {N : Nat}
  [Fact (2 < N)]
  {z : ZMod N × ZMod N}
  {a b : Fin 6}
-- given
  (hrank : (triangularTorusDirectionRank a).val + 1 = (triangularTorusDirectionRank b).val ∨ (triangularTorusDirectionRank b).val + 1 = (triangularTorusDirectionRank a).val) :
-- imply
  (triangularTorusGraph N).Adj (z + (((triangularTorusSplitOffset a).1 : ZMod N), ((triangularTorusSplitOffset a).2 : ZMod N))) (z + (((triangularTorusSplitOffset b).1 : ZMod N), ((triangularTorusSplitOffset b).2 : ZMod N))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitOffset_adj_of_rank N z a b hrank

/--
[triangularTorusSplitEmbedVertex_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_matching_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : KWDartPort (triangularTorusGraph L)}
-- given
  (hmatch : kwDartOfPort (triangularTorusGraph L) q = (kwDartOfPort (triangularTorusGraph L) p).symm) :
-- imply
  triangularTorusSplitEmbedVertex L q = triangularTorusSplitEmbedVertex L p + (((triangularIntStep (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).1 : ZMod (3 * L)), ((triangularIntStep (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).2 : ZMod (3 * L))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_matching L hmatch

/--
[triangularTorusSplitEmbedVertex_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedVertex_adj_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : KWDartPort (triangularTorusGraph L)}
-- given
  (hpq : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Adj p q) :
-- imply
  (triangularTorusGraph (3 * L)).Adj (triangularTorusSplitEmbedVertex L p) (triangularTorusSplitEmbedVertex L q) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedVertex_adj L hpq

/--
[triangularTorusSplitEmbedHom_mapDart_of_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedHom_mapDart_of_matching_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd = (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
-- imply
  (triangularTorusSplitEmbedHom L).mapDart d = triangularTorusDartEquiv (3 * L) (triangularTorusSplitEmbedVertex L d.fst, triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) d.fst)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedHom_mapDart_of_matching L d hmatching

/--
[triangularTorusSplitEmbedWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_support_eq
  {L : Nat}
  [Fact (2 < L)]
  {u v : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u v} :
-- imply
  (triangularTorusSplitEmbedWalk L p).support = p.support.map (triangularTorusSplitEmbedVertex L) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_support L p

/--
[triangularTorusSplitEmbedWalk_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_edges_eq
  {L : Nat}
  [Fact (2 < L)]
  {u v : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u v} :
-- imply
  (triangularTorusSplitEmbedWalk L p).edges = p.edges.map (Sym2.map (triangularTorusSplitEmbedHom L)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_edges L p

/--
[triangularTorusSplitEmbedWalk_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_isCycle_eq
  {L : Nat}
  [Fact (2 < L)]
  {u : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u u}
-- given
  (hp : p.IsCycle) :
-- imply
  (triangularTorusSplitEmbedWalk L p).IsCycle := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_isCycle L p hp

/--
[triangularTorusSplitEmbedWalk_verts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_verts_disjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {u v : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u u}
  {q : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk v v}
-- given
  (hdisjoint : Disjoint p.toSubgraph.verts q.toSubgraph.verts) :
-- imply
  Disjoint (triangularTorusSplitEmbedWalk L p).toSubgraph.verts (triangularTorusSplitEmbedWalk L q).toSubgraph.verts := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_verts_disjoint L p q hdisjoint


-- created on 2026-10-23
