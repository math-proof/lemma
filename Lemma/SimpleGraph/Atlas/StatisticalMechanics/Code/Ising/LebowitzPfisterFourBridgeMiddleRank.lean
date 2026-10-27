import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMiddleRank
open StatMech StatMech.Ising


/--
[fourBridgeAgreementSpinMass_sum_five_levels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMiddleRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_sum_five_levels_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z (-4) + fourBridgeAgreementSpinMass G J hf w x y z (-2) + fourBridgeAgreementSpinMass G J hf w x y z 0 + fourBridgeAgreementSpinMass G J hf w x y z 2 + fourBridgeAgreementSpinMass G J hf w x y z 4 = 1 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_sum_five_levels G J hf w x y z

/--
[fourBridgeAgreementSpinMass_zero_eq_marginal_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMiddleRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_zero_eq_marginal_pairs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z 0 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, x} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, y} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, z} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, y} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, z} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y, z} := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_zero_eq_marginal_pairs G J hf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementSpinMass_zero_eq_rankMass_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMiddleRank.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_zero_eq_rankMass_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeAgreementSpinMass G J hf w x y z 0 = fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_zero_eq_rankMass_two G J hf w x y z

/--
[fourBridgeRankMass_two_eq_marginal_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMiddleRank.lean)
-/
@[path]
private lemma fourBridgeRankMass_two_eq_marginal_pairs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, x} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, y} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w, z} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, y} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x, z} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y, z} := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_two_eq_marginal_pairs G J hf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
