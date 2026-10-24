import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAngularPortExternal
open StatMech StatMech.FrontierA


/--
[KWAngularPortRadiusData.trimParameter_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma trimParameter_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d : G.Dart} :
-- imply
  0 < data.trimParameter d := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.trimParameter_pos data d

/--
[KWAngularPortRadiusData.trimParameter_lt_quarter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma trimParameter_lt_quarter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d : G.Dart} :
-- imply
  data.trimParameter d < 1 / 4 := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.trimParameter_lt_quarter data d

/--
[KWAngularPortRadiusData.trimParameter_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma trimParameter_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {d : G.Dart} :
-- imply
  data.trimParameter d.symm = data.trimParameter d := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.trimParameter_symm data d

/--
[KWAngularPortRadiusData.portVertex_eq_lineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma portVertex_eq_lineMap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p : KWDartPort G} :
-- imply
  kwAngularPortVertex embedding (data.radius : ℝ) p = AffineMap.lineMap (embedding.vertex (kwDartOfPort G p).fst) (embedding.vertex (kwDartOfPort G p).snd) (data.trimParameter (kwDartOfPort G p)) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.portVertex_eq_lineMap data p

/--
[kw_lineMap_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma kw_lineMap_reverse_eq
  {a b : ℂ}
  {t : ℝ} :
-- imply
  AffineMap.lineMap b a t = AffineMap.lineMap a b (1 - t) := by
-- proof
  apply StatMech.FrontierA.kw_lineMap_reverse a b t

/--
[KWAngularPortRadiusData.matchingPortVertex_eq_lineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma matchingPortVertex_eq_lineMap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q : KWDartPort G}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
-- imply
  kwAngularPortVertex embedding (data.radius : ℝ) q = AffineMap.lineMap (embedding.vertex (kwDartOfPort G p).fst) (embedding.vertex (kwDartOfPort G p).snd) (1 - data.trimParameter (kwDartOfPort G p)) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.matchingPortVertex_eq_lineMap data hmatching

/--
[kw_lineMap_lineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma kw_lineMap_lineMap_eq
  {a b : ℂ}
  {t u : ℝ} :
-- imply
  AffineMap.lineMap (AffineMap.lineMap a b t) (AffineMap.lineMap a b (1 - t)) u = AffineMap.lineMap a b (t + u * (1 - 2 * t)) := by
-- proof
  apply StatMech.FrontierA.kw_lineMap_lineMap a b t u

/--
[KWAngularPortRadiusData.matching_sbtw_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma matching_sbtw_original_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q : KWDartPort G}
  {z : ℂ}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
  (hz : Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p) z (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
-- imply
  Sbtw ℝ (embedding.vertex (kwDartOfPort G p).fst) z (embedding.vertex (kwDartOfPort G p).snd) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.matching_sbtw_original data hmatching hz

/--
[KWAngularPortRadiusData.radius_lt_dist_fst_of_matching_sbtw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma radius_lt_dist_fst_of_matching_sbtw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q : KWDartPort G}
  {z : ℂ}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
  (hz : Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p) z (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
-- imply
  (data.radius : ℝ) < dist (embedding.vertex (kwDartOfPort G p).fst) z := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.radius_lt_dist_fst_of_matching_sbtw data hmatching hz

/--
[KWAngularPortRadiusData.radius_lt_dist_snd_of_matching_sbtw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortExternal.lean)
-/
@[path]
private lemma radius_lt_dist_snd_of_matching_sbtw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q : KWDartPort G}
  {z : ℂ}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
  (hz : Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p) z (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
-- imply
  (data.radius : ℝ) < dist (embedding.vertex (kwDartOfPort G p).snd) z := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.radius_lt_dist_snd_of_matching_sbtw data hmatching hz


-- created on 2026-10-23
