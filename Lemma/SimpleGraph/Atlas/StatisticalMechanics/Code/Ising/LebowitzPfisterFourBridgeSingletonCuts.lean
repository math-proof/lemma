import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSingletonCuts
open Finset StatMech StatMech.Ising


/--
[fourBridgeRankMass_zero_eq_marginal_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeRankMass_zero_eq_marginal_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 0 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) ∅ := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_zero_eq_marginal_empty G J hf w x y z

/--
[fourBridgeRankMass_four_eq_marginal_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeRankMass_four_eq_marginal_full_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z) := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_four_eq_marginal_full G J hf w x y z

/--
[ghsiAgreementMarginalProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma ghsiAgreementMarginalProb_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiAgreementMarginalProb G J hf M P <= 1 := by
-- proof
  apply StatMech.Ising.ghsiAgreementMarginalProb_le_one G J hf M P

/--
[fourBridgeRankMass_one_eq_marginal_singletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeRankMass_one_eq_marginal_singletons_eq
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
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {w} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {x} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {y} + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) {z} := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_one_eq_marginal_singletons G J hf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeRankMass_three_eq_marginal_cosingletons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeRankMass_three_eq_marginal_cosingletons_eq
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
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 3 = ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {w}) + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {x}) + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {y}) + ghsiAgreementMarginalProb G J hf (fourBridgeMarkedSet w x y z) (fourBridgeMarkedSet w x y z \ {z}) := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_three_eq_marginal_cosingletons G J hf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementMarginal_singletonPair_sum_le_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeAgreementMarginal_singletonPair_sum_le_rank_eq
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
  let M := fourBridgeMarkedSet w x y z let mu := ghsiAgreementMarginalProb G J hf M let p := fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) mu {w} * mu {x} + mu {w} * mu {y} + mu {w} * mu {z} + mu {x} * mu {y} + mu {x} * mu {z} + mu {y} * mu {z} <= mu ∅ * p 2 := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementMarginal_singletonPair_sum_le_rank G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeRankMass_one_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeRankMass_one_sq_le_eq
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
  let p := fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) p 1 ^ 2 <= p 1 + 2 * p 0 * p 2 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_one_sq_le G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementMarginal_cosingletonPair_sum_le_rank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeAgreementMarginal_cosingletonPair_sum_le_rank_eq
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
  let M := fourBridgeMarkedSet w x y z let mu := ghsiAgreementMarginalProb G J hf M let p := fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) mu (M \ {w}) * mu (M \ {x}) + mu (M \ {w}) * mu (M \ {y}) + mu (M \ {w}) * mu (M \ {z}) + mu (M \ {x}) * mu (M \ {y}) + mu (M \ {x}) * mu (M \ {z}) + mu (M \ {y}) * mu (M \ {z}) <= p 2 * mu M := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementMarginal_cosingletonPair_sum_le_rank G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeRankMass_three_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeRankMass_three_sq_le_eq
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
  let p := fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) p 3 ^ 2 <= p 3 + 2 * p 2 * p 4 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_three_sq_le G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeAgreementMarginal_nestedSingletonPair_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeAgreementMarginal_nestedSingletonPair_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v) :
-- imply
  let M := fourBridgeMarkedSet w x y z let mu := ghsiAgreementMarginalProb G J hf M (mu {w} + mu {x}) * mu (M \ {w, x}) + (mu {w} + mu {y}) * mu (M \ {w, y}) + (mu {w} + mu {z}) * mu (M \ {w, z}) + (mu {x} + mu {y}) * mu (M \ {x, y}) + (mu {x} + mu {z}) * mu (M \ {x, z}) + (mu {y} + mu {z}) * mu (M \ {y, z}) <= mu {w, x} * (mu (M \ {w}) + mu (M \ {x})) + mu {w, y} * (mu (M \ {w}) + mu (M \ {y})) + mu {w, z} * (mu (M \ {w}) + mu (M \ {z})) + mu {x, y} * (mu (M \ {x}) + mu (M \ {y})) + mu {x, z} * (mu (M \ {x}) + mu (M \ {z})) + mu {y, z} * (mu (M \ {y}) + mu (M \ {z})) := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementMarginal_nestedSingletonPair_sum_le G J hf hJ hhf

/--
[fourBridgeAgreementMarginal_intersectingPair_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSingletonCuts.lean)
-/
@[path]
private lemma fourBridgeAgreementMarginal_intersectingPair_sum_le_eq
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
  let M := fourBridgeMarkedSet w x y z let mu := ghsiAgreementMarginalProb G J hf M mu {w, x} * mu {w, y} + mu {x, w} * mu {x, y} + mu {y, w} * mu {y, x} + mu {w, x} * mu {w, z} + mu {x, w} * mu {x, z} + mu {z, w} * mu {z, x} + mu {w, y} * mu {w, z} + mu {y, w} * mu {y, z} + mu {z, w} * mu {z, y} + mu {x, y} * mu {x, z} + mu {y, x} * mu {y, z} + mu {z, x} * mu {z, y} <= mu {w} * mu {w, x, y} + mu {x} * mu {x, w, y} + mu {y} * mu {y, w, x} + mu {w} * mu {w, x, z} + mu {x} * mu {x, w, z} + mu {z} * mu {z, w, x} + mu {w} * mu {w, y, z} + mu {y} * mu {y, w, z} + mu {z} * mu {z, w, y} + mu {x} * mu {x, y, z} + mu {y} * mu {y, x, z} + mu {z} * mu {z, x, y} := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementMarginal_intersectingPair_sum_le G J hf hJ hhf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
