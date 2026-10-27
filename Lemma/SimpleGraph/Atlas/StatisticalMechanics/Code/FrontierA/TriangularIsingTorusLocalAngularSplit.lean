import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4
open StatMech StatMech.FrontierA


/--
[triangularTorusOutgoingDart_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean)
-/
@[path]
private lemma triangularTorusOutgoingDart_card_eq
  {L : Nat}
  [Fact (2 < L)]
  {v : ZMod L × ZMod L} :
-- imply
  Fintype.card (KWOutgoingDart (G := triangularTorusGraph L) v) = 6 := by
-- proof
  apply StatMech.FrontierA.triangularTorusOutgoingDart_card L v

/--
[triangularTorusLocalPortOrder_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean)
-/
@[path]
private lemma triangularTorusLocalPortOrder_rank_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : KWDartPort (triangularTorusGraph L)} :
-- imply
  kwOrderedPortRank (triangularTorusLocalPortOrder L) p = (triangularTorusDirectionRank (triangularTorusGraphDartDirection L (kwDartOfPort (triangularTorusGraph L) p))).val := by
-- proof
  apply StatMech.FrontierA.triangularTorusLocalPortOrder_rank L p

/--
[triangularTorusGraphDartDirection_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean)
-/
@[path]
private lemma triangularTorusGraphDartDirection_symm_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : (triangularTorusGraph L).Dart} :
-- imply
  triangularTorusGraphDartDirection L d.symm = triangularTorusDirectionReverse (triangularTorusGraphDartDirection L d) := by
-- proof
  apply StatMech.FrontierA.triangularTorusGraphDartDirection_symm L d

/--
[triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean)
-/
@[path]
private lemma triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt_eq
  {rho : Complex}
  {a b : Fin 6}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hrank : (triangularTorusDirectionRank (triangularTorusDirectionReverse a)).val < (triangularTorusDirectionRank b).val) :
-- imply
  triangularKacWardTurnMatrix rho a b = -Complex.I * (rho ^ triangularTorusDirectionSignedAngle (triangularTorusDirectionReverse a))⁻¹ * rho ^ triangularTorusDirectionSignedAngle b := by
-- proof
  apply StatMech.FrontierA.triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt rho hrho a b hrank

/--
[triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean)
-/
@[path]
private lemma triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt_eq
  {rho : Complex}
  {a b : Fin 6}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hrank : (triangularTorusDirectionRank b).val < (triangularTorusDirectionRank (triangularTorusDirectionReverse a)).val) :
-- imply
  triangularKacWardTurnMatrix rho a b = Complex.I * (rho ^ triangularTorusDirectionSignedAngle (triangularTorusDirectionReverse a))⁻¹ * rho ^ triangularTorusDirectionSignedAngle b := by
-- proof
  apply StatMech.FrontierA.triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt rho hrho a b hrank

/--
[triangularTorus_localAngularSplit_det_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean)
-/
@[path]
private lemma triangularTorus_localAngularSplit_det_eq_original_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (weight : Sym2 (ZMod L × ZMod L) -> Complex) :
-- imply
  (1 - kwGraphTransition (kwOrderedDartPortSplitGraph (triangularTorusGraph L) (triangularTorusLocalPortOrder L)) (kwOrderedSplitWeight (triangularTorusGraph L) weight) (kwLocalAngularSplitPhase (triangularTorusLocalAngularData L rho hrho))).det = (1 - kwGraphTransition (triangularTorusGraph L) weight (triangularTorusGraphPhase L rho 1 1)).det := by
-- proof
  apply StatMech.FrontierA.triangularTorus_localAngularSplit_det_eq_original L rho hrho weight


-- created on 2026-10-23
