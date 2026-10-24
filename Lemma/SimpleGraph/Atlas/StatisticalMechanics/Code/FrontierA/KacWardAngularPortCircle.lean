import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAngularPortCircle
open StatMech StatMech.FrontierA


/--
[kwAngularUnit_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kwAngularUnit_re_eq
  {a : ℝ} :
-- imply
  (kwAngularUnit a).re = Real.cos a := by
-- proof
  apply StatMech.FrontierA.kwAngularUnit_re a

/--
[kwAngularUnit_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kwAngularUnit_im_eq
  {a : ℝ} :
-- imply
  (kwAngularUnit a).im = Real.sin a := by
-- proof
  apply StatMech.FrontierA.kwAngularUnit_im a

/--
[KWStraightLineEmbedding.dartUnit_eq_angularUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma dartUnit_eq_angularUnit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d : G.Dart} :
-- imply
  embedding.dartUnit d = kwAngularUnit (embedding.dartAngle d).toReal := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.dartUnit_eq_angularUnit embedding d

/--
[kw_sin_add_sub_sin_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kw_sin_add_sub_sin_add_eq
  {x y : ℝ} :
-- imply
  Real.sin x + Real.sin y - Real.sin (x + y) = 4 * Real.sin (x / 2) * Real.sin (y / 2) * Real.sin ((x + y) / 2) := by
-- proof
  apply StatMech.FrontierA.kw_sin_add_sub_sin_add x y

/--
[kwComplexCross_angularUnit_chord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kwComplexCross_angularUnit_chord_eq
  {a b c : ℝ} :
-- imply
  kwComplexCross (kwAngularUnit b - kwAngularUnit a) (kwAngularUnit c - kwAngularUnit a) = 4 * Real.sin ((b - a) / 2) * Real.sin ((c - b) / 2) * Real.sin ((c - a) / 2) := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_angularUnit_chord a b c

/--
[kwComplexCross_angularUnit_chord_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kwComplexCross_angularUnit_chord_pos_eq
  {a b c : ℝ}
-- given
  (ha : -Real.pi < a)
  (hb : b ≤ Real.pi)
  (hcLower : -Real.pi < c)
  (hcUpper : c ≤ Real.pi)
  (hab : a < b)
  (hc : c < a ∨ b < c) :
-- imply
  0 < kwComplexCross (kwAngularUnit b - kwAngularUnit a) (kwAngularUnit c - kwAngularUnit a) := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_angularUnit_chord_pos ha hb hcLower hcUpper hab hc

/--
[kwOrderedPortRank_eq_iff_of_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kwOrderedPortRank_eq_iff_of_owner_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {order : KWPortOrder G}
  {p q : KWDartPort G}
-- given
  (howner : p.1 = q.1) :
-- imply
  kwOrderedPortRank order p = kwOrderedPortRank order q ↔ p = q := by
-- proof
  apply StatMech.FrontierA.kwOrderedPortRank_eq_iff_of_owner order howner

/--
[KWStraightLineEmbedding.angularPort_supporting_cross_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma angularPort_supporting_cross_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {p q s : KWDartPort G}
-- given
  (hpqOwner : p.1 = q.1)
  (hpsOwner : p.1 = s.1)
  (hpq : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 = kwOrderedPortRank (kwAngularPortOrder embedding) q)
  (hsp : s ≠ p)
  (hsq : s ≠ q) :
-- imply
  0 < kwComplexCross (embedding.dartUnit (kwDartOfPort G q) - embedding.dartUnit (kwDartOfPort G p)) (embedding.dartUnit (kwDartOfPort G s) - embedding.dartUnit (kwDartOfPort G p)) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.angularPort_supporting_cross_pos embedding hpqOwner hpsOwner hpq hsp hsq

/--
[kwComplexCross_ofReal_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma kwComplexCross_ofReal_mul_eq
  {r : ℝ}
  {x y : ℂ} :
-- imply
  kwComplexCross ((r : ℂ) * x) ((r : ℂ) * y) = r ^ 2 * kwComplexCross x y := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_ofReal_mul r x y

/--
[KWAngularPortRadiusData.portVertex_supporting_cross_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma portVertex_supporting_cross_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q s : KWDartPort G}
-- given
  (hpqOwner : p.1 = q.1)
  (hpsOwner : p.1 = s.1)
  (hpq : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 = kwOrderedPortRank (kwAngularPortOrder embedding) q)
  (hsp : s ≠ p)
  (hsq : s ≠ q) :
-- imply
  0 < kwComplexCross (kwAngularPortVertex embedding (data.radius : ℝ) q - kwAngularPortVertex embedding (data.radius : ℝ) p) (kwAngularPortVertex embedding (data.radius : ℝ) s - kwAngularPortVertex embedding (data.radius : ℝ) p) := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.portVertex_supporting_cross_pos data hpqOwner hpsOwner hpq hsp hsq

/--
[KWAngularPortRadiusData.internalChords_disjoint_of_same_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortCircle.lean)
-/
@[path]
private lemma internalChords_disjoint_of_same_owner_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {data : KWAngularPortRadiusData embedding}
  {p q p' q' : KWDartPort G}
-- given
  (hpqOwner : p.1 = q.1)
  (hppOwner : p.1 = p'.1)
  (hpq'Owner : p.1 = q'.1)
  (hpq : kwOrderedPortRank (kwAngularPortOrder embedding) p + 1 = kwOrderedPortRank (kwAngularPortOrder embedding) q)
  (hpq' : kwOrderedPortRank (kwAngularPortOrder embedding) p' + 1 = kwOrderedPortRank (kwAngularPortOrder embedding) q')
  (hedge : s(p, q) ≠ s(p', q')) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p) z (kwAngularPortVertex embedding (data.radius : ℝ) q)} {z : ℂ | Sbtw ℝ (kwAngularPortVertex embedding (data.radius : ℝ) p') z (kwAngularPortVertex embedding (data.radius : ℝ) q')} := by
-- proof
  apply StatMech.FrontierA.KWAngularPortRadiusData.internalChords_disjoint_of_same_owner data hpqOwner hppOwner hpq'Owner hpq hpq' hedge


-- created on 2026-10-23
