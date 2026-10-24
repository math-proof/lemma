import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
open StatMech StatMech.FrontierA


/--
[oddCubicalCenteredSite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalPlusCorrDecay.lean)
-/
@[path]
private lemma oddCubicalCenteredSite_zero_eq
  {m : Nat}
  {q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)} :
-- imply
  oddCubicalCenteredSite m q 0 = (q.x.val : Int) - m := by
-- proof
  apply StatMech.FrontierA.oddCubicalCenteredSite_zero m q

/--
[oddCubicalCenteredSite_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalPlusCorrDecay.lean)
-/
@[path]
private lemma oddCubicalCenteredSite_one_eq
  {m : Nat}
  {q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)} :
-- imply
  oddCubicalCenteredSite m q 1 = (q.y.val : Int) - m := by
-- proof
  apply StatMech.FrontierA.oddCubicalCenteredSite_one m q

/--
[oddCubicalCenteredSite_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalPlusCorrDecay.lean)
-/
@[path]
private lemma oddCubicalCenteredSite_two_eq
  {m : Nat}
  {q : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)} :
-- imply
  oddCubicalCenteredSite m q 2 = (m : Int) - q.z.val := by
-- proof
  apply StatMech.FrontierA.oddCubicalCenteredSite_two m q

/--
[l1dist_oddCubicalCenteredSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalPlusCorrDecay.lean)
-/
@[path]
private lemma l1dist_oddCubicalCenteredSite_eq
  {m : Nat}
  {q r : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)} :
-- imply
  l1dist 3 (oddCubicalCenteredSite m q) (oddCubicalCenteredSite m r) = cubicalDualL1 (some q) (some r) := by
-- proof
  apply StatMech.FrontierA.l1dist_oddCubicalCenteredSite m q r

/--
[plusCorr_oddCubical_exponential_of_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalPlusCorrDecay.lean)
-/
@[path]
private lemma plusCorr_oddCubical_exponential_of_lt_betaC_eq
  {beta : Real}
-- given
  (hbeta : 0 <= beta)
  (hlt : beta < betaC 3) :
-- imply
  exists c, 0 < c /\ forall m (q r : CubicalCell (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)), plusCorr 3 beta (oddCubicalCenteredSite m q) (oddCubicalCenteredSite m r) <= Real.exp (-c * (cubicalDualL1 (some q) (some r) : Real)) := by
-- proof
  apply StatMech.FrontierA.plusCorr_oddCubical_exponential_of_lt_betaC hbeta hlt


-- created on 2026-10-23
