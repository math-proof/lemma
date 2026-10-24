import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopDefectEdgeRooted
open Finset SimpleGraph Filter StatMech StatMech.Onsager


/--
[coe_ons_defectEdgeX_eq_kwEvenPolynomial_added](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma coe_ons_defectEdgeX_eq_kwEvenPolynomial_added_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {x z : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v) :
-- imply
  (ons_defectEdgeX G u v x z : Complex) = kwEvenPolynomial (onsDefectEdgeGraph G u v) (kwScaleGraphEdgeWeight (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv).edge (z : Complex)) := by
-- proof
  apply StatMech.Onsager.coe_ons_defectEdgeX_eq_kwEvenPolynomial_added huv hnotAdj x z

/--
[ons_kwAddedEdgeEvenBase_defect_eq_ons_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma ons_kwAddedEdgeEvenBase_defect_eq_ons_X_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {x : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v) :
-- imply
  ons_kwAddedEdgeEvenBase (onsDefectEdgeGraph G u v) (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) = (ons_X G x : Complex) := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeEvenBase_defect_eq_ons_X huv hnotAdj x

/--
[ons_kwAddedEdgeEvenSource_defect_eq_sourceX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma ons_kwAddedEdgeEvenSource_defect_eq_sourceX_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {x : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v) :
-- imply
  ons_kwAddedEdgeEvenSource (onsDefectEdgeGraph G u v) (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) = (ons_sourceX G {u, v} x : Complex) := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeEvenSource_defect_eq_sourceX huv hnotAdj x

/--
[ons_kwAddedEdgeRoot_zero_defect_eq_ons_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma ons_kwAddedEdgeRoot_zero_defect_eq_ons_X_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v)}
  {x : Real}
  {q : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v)
  (hx : 0 ≤ x)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) * q < 1) :
-- imply
  ons_kwAddedEdgeRoot (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) 0 = (ons_X G x : Complex) := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeRoot_zero_defect_eq_ons_X huv hnotAdj embedding hx q hq hentry hsmall hcard

/--
[ons_kwAddedEdgeNormalizedSource_defect_eq_sourceX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma ons_kwAddedEdgeNormalizedSource_defect_eq_sourceX_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v)}
  {x : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v)
  (hx : 0 ≤ x)
  (hbranch : ons_kwAddedEdgeRoot (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) 0 = (ons_X G x : Complex)) :
-- imply
  ons_kwAddedEdgeNormalizedSource (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) = (ons_sourceX G {u, v} x : Complex) := by
-- proof
  apply StatMech.Onsager.ons_kwAddedEdgeNormalizedSource_defect_eq_sourceX huv hnotAdj embedding hx hbranch

/--
[coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v)}
  {x : Real}
  {q : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v)
  (hx : 0 ≤ x)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) * q < 1)
  (hbranch : ons_kwAddedEdgeRoot (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) 0 = (ons_X G x : Complex)) :
-- imply
  (ons_sourceX G {u, v} x : Complex) = -(ons_kwAddedEdgeDeletedRoot (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) * ons_kwAddedEdgeRootedSeries (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv)) := by
-- proof
  apply StatMech.Onsager.coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect huv hnotAdj embedding hx q hq hentry hsmall hcard hbranch

/--
[coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect_of_small](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean)
-/
@[path]
private lemma coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect_of_small_eq
  [Fintype V]
  [DecidableEq V]
  {u v : V}
  {embedding : KWStraightLineEmbedding (onsDefectEdgeGraph G u v)}
  {x : Real}
  {q : Real}
-- given
  (huv : u ≠ v)
  (hnotAdj : ¬ G.Adj u v)
  (hx : 0 ≤ x)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖ons_kwAddedEdgeBaseMatrix (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) dart next‖ ≤ q)
  (hsmall : q < (2 * (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) ^ 2)⁻¹)
  (hcard : (Fintype.card (onsDefectEdgeGraph G u v).Dart : Real) * q < 1) :
-- imply
  (ons_sourceX G {u, v} x : Complex) = -(ons_kwAddedEdgeDeletedRoot (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv) * ons_kwAddedEdgeRootedSeries (onsDefectEdgeGraph G u v) embedding (onsDefectEdgeAddedWeight u v x) (onsDefectEdgeDart G huv)) := by
-- proof
  apply StatMech.Onsager.coe_ons_sourceX_eq_neg_deleted_mul_rooted_defect_of_small huv hnotAdj embedding hx q hq hentry hsmall hcard


-- created on 2026-10-23
