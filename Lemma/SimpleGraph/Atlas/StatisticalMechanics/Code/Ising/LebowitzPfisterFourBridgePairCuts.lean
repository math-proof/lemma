import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePairCuts
open Finset StatMech StatMech.Ising


/--
[fourBridgeAgreementMarginal_complementaryPair_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePairCuts.lean)
-/
@[path]
private lemma fourBridgeAgreementMarginal_complementaryPair_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  let M := fourBridgeMarkedSet w x y z ghsiAgreementMarginalProb G J hf M {w, x} * ghsiAgreementMarginalProb G J hf M {y, z} + ghsiAgreementMarginalProb G J hf M {w, y} * ghsiAgreementMarginalProb G J hf M {x, z} + ghsiAgreementMarginalProb G J hf M {w, z} * ghsiAgreementMarginalProb G J hf M {x, y} <= 3 * ghsiAgreementMarginalProb G J hf M ∅ * ghsiAgreementMarginalProb G J hf M M := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementMarginal_complementaryPair_sum_le G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementMarginal_complementaryPair_sum_le_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePairCuts.lean)
-/
@[path]
private lemma fourBridgeAgreementMarginal_complementaryPair_sum_le_rank_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  let M := fourBridgeMarkedSet w x y z let p := fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) ghsiAgreementMarginalProb G J hf M {w, x} * ghsiAgreementMarginalProb G J hf M {y, z} + ghsiAgreementMarginalProb G J hf M {w, y} * ghsiAgreementMarginalProb G J hf M {x, z} + ghsiAgreementMarginalProb G J hf M {w, z} * ghsiAgreementMarginalProb G J hf M {x, y} <= 3 * p 0 * p 4 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementMarginal_complementaryPair_sum_le_rank G J hf hJ hhf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
