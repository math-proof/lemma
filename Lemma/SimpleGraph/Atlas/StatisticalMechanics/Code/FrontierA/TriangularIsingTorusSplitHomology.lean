import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitHomology
open StatMech StatMech.FrontierA


/--
[triangular_three_valCoord_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangular_three_valCoord_eq_zero_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L}
  {c : Nat}
-- given
  (hc : c < 3) :
-- imply
  ((3 * z.val + c : Nat) : ZMod (3 * L)) = 0 ↔ z = 0 ∧ c = 0 := by
-- proof
  apply StatMech.FrontierA.triangular_three_valCoord_eq_zero_iff L z c hc

/--
[triangular_three_valCoord_eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangular_three_valCoord_eq_neg_one_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L}
  {c : Nat}
-- given
  (hc : c < 3) :
-- imply
  ((3 * z.val + c : Nat) : ZMod (3 * L)) = -1 ↔ z = -1 ∧ c = 2 := by
-- proof
  apply StatMech.FrontierA.triangular_three_valCoord_eq_neg_one_iff L z c hc

/--
[triangular_three_zmodCast_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangular_three_zmodCast_eq_zero_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (3 : ZMod (3 * L)) * ZMod.cast z = 0 ↔ z = 0 := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_eq_zero_iff L z

/--
[triangular_three_zmodCast_add_two_eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangular_three_zmodCast_add_two_eq_neg_one_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L} :
-- imply
  (3 : ZMod (3 * L)) * ZMod.cast z + 2 = -1 ↔ z = -1 := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_add_two_eq_neg_one_iff L z

/--
[triangular_three_zmodCast_add_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangular_three_zmodCast_add_eq_zero_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L}
  {c : Nat}
-- given
  (hc : c < 3) :
-- imply
  (3 : ZMod (3 * L)) * ZMod.cast z + c = 0 ↔ z = 0 ∧ c = 0 := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_add_eq_zero_iff L z c hc

/--
[triangular_three_zmodCast_add_eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangular_three_zmodCast_add_eq_neg_one_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {z : ZMod L}
  {c : Nat}
-- given
  (hc : c < 3) :
-- imply
  (3 : ZMod (3 * L)) * ZMod.cast z + c = -1 ↔ z = -1 ∧ c = 2 := by
-- proof
  apply StatMech.FrontierA.triangular_three_zmodCast_add_eq_neg_one_iff L z c hc

/--
[triangularTorusSplitEmbed_matching_xWrap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_matching_xWrap_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  let a := triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p) ons_xWrap (triangularTorusXMovementDart (3 * L) (triangularTorusSplitEmbedVertex L p, a)) ↔ ons_xWrap (triangularTorusXMovementDart L (p.1, a)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_matching_xWrap_iff L p

/--
[triangularTorusSplitEmbed_matching_yWrap_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_matching_yWrap_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  let a := triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p) ons_yWrap (triangularTorusYMovementDart (3 * L) (triangularTorusSplitEmbedVertex L p, a)) ↔ ons_yWrap (triangularTorusYMovementDart L (p.1, a)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_matching_yWrap_iff L p

/--
[triangularTorusDartEquiv_portDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusDartEquiv_portDirection_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  triangularTorusDartEquiv L (p.1, triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p)) = kwDartOfPort (triangularTorusGraph L) p := by
-- proof
  apply StatMech.FrontierA.triangularTorusDartEquiv_portDirection L p

/--
[triangularTorusSplitEdgeProjection_eq_portDartEdge_of_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEdgeProjection_eq_portDartEdge_of_matching_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd = (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
-- imply
  kwOrderedSplitEdgeProjection d.edge = (kwDartOfPort (triangularTorusGraph L) d.fst).edge := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEdgeProjection_eq_portDartEdge_of_matching L d hmatching

/--
[triangularTorusSplitEmbed_matching_xSeam_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_matching_xSeam_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd = (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
-- imply
  triangularTorusXSeamEdge (3 * L) ((triangularTorusSplitEmbedHom L).mapDart d).edge ↔ triangularTorusXSeamEdge L (kwOrderedSplitEdgeProjection d.edge) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_matching_xSeam_iff L d hmatching

/--
[triangularTorusSplitEmbed_matching_ySeam_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_matching_ySeam_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd = (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
-- imply
  triangularTorusYSeamEdge (3 * L) ((triangularTorusSplitEmbedHom L).mapDart d).edge ↔ triangularTorusYSeamEdge L (kwOrderedSplitEdgeProjection d.edge) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_matching_ySeam_iff L d hmatching

/--
[triangularTorusSplitEmbed_matching_edgeClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_matching_edgeClass_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hmatching : kwDartOfPort (triangularTorusGraph L) d.snd = (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
-- imply
  triangularTorusSurfaceEdgeClass (3 * L) ((triangularTorusSplitEmbedHom L).mapDart d).edge = kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L) d.edge := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_matching_edgeClass L d hmatching

/--
[triangularTorusSplitEmbed_sameCenter_not_xSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_sameCenter_not_xSeam_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : KWDartPort (triangularTorusGraph L)}
-- given
  (hcenter : p.1 = q.1) :
-- imply
  ¬triangularTorusXSeamEdge (3 * L) s(triangularTorusSplitEmbedVertex L p, triangularTorusSplitEmbedVertex L q) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_sameCenter_not_xSeam L p q hcenter

/--
[triangularTorusSplitEmbed_sameCenter_not_ySeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_sameCenter_not_ySeam_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : KWDartPort (triangularTorusGraph L)}
-- given
  (hcenter : p.1 = q.1) :
-- imply
  ¬ triangularTorusYSeamEdge (3 * L) s(triangularTorusSplitEmbedVertex L p, triangularTorusSplitEmbedVertex L q) := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_sameCenter_not_ySeam L p q hcenter

/--
[triangularTorusSplitEmbed_internal_edgeClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_internal_edgeClass_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart}
-- given
  (hinternal : ¬kwDartOfPort (triangularTorusGraph L) d.snd = (kwDartOfPort (triangularTorusGraph L) d.fst).symm) :
-- imply
  triangularTorusSurfaceEdgeClass (3 * L) ((triangularTorusSplitEmbedHom L).mapDart d).edge = kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L) d.edge := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_internal_edgeClass L d hinternal

/--
[triangularTorusSplitEmbed_edgeClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbed_edgeClass_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Dart} :
-- imply
  triangularTorusSurfaceEdgeClass (3 * L) ((triangularTorusSplitEmbedHom L).mapDart d).edge = kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L) d.edge := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbed_edgeClass L d

/--
[triangularTorusSplitEmbedWalk_surfaceHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitHomology.lean)
-/
@[path]
private lemma triangularTorusSplitEmbedWalk_surfaceHomology_eq
  {L : Nat}
  [Fact (2 < L)]
  {u v : KWDartPort (triangularTorusGraph L)}
  {p : (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)).Walk u v} :
-- imply
  surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass (3 * L)) (triangularTorusSplitEmbedWalk L p).edges.toFinset = surfaceSubgraphHomology (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L)) p.edges.toFinset := by
-- proof
  apply StatMech.FrontierA.triangularTorusSplitEmbedWalk_surfaceHomology L p


-- created on 2026-10-23
