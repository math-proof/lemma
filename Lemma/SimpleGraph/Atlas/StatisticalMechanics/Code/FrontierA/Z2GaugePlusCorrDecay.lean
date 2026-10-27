import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePlusCorrDecay
open StatMech StatMech.FrontierA


/--
[plusCorr_allPairs_exponential_of_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePlusCorrDecay.lean)
-/
@[path]
private lemma plusCorr_allPairs_exponential_of_lt_betaC_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta : 0 <= beta)
  (hlt : beta < betaC d) :
-- imply
  exists c, 0 < c /\ forall x y : Site d, plusCorr d beta x y <= Real.exp (-c * (l1dist d x y : Real)) := by
-- proof
  apply StatMech.FrontierA.plusCorr_allPairs_exponential_of_lt_betaC hd hbeta hlt


-- created on 2026-10-23
