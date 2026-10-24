import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleHighRank
open StatMech StatMech.Ising


/--
[fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleHighRank.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_two_le_eq
  {a b d : Real}
-- given
  (ha2 : 2 <= a)
  (hp1 : 0 <= fourBridgeRankMass a b (1 - a + b + d) d 1)
  (hp2 : 0 <= fourBridgeRankMass a b (1 - a + b + d) d 2)
  (hp3 : 0 <= fourBridgeRankMass a b (1 - a + b + d) d 3) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b (1 - a + b + d) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_two_le ha2 hp1 hp2 hp3

/--
[fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleHighRank.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_two_le_eq
  {a b d : Real}
-- given
  (ha2 : 2 <= a)
  (hp0 : 0 <= fourBridgeRankMass a b (2 + a - 2 * d) d 0)
  (hp1 : 0 <= fourBridgeRankMass a b (2 + a - 2 * d) d 1)
  (hp2 : 0 <= fourBridgeRankMass a b (2 + a - 2 * d) d 2) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b (2 + a - 2 * d) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_two_le ha2 hp0 hp1 hp2

/--
[fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_two_le_oneCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleHighRank.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_two_le_oneCoeff_eq
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
  (hyz : y ≠ z)
  (ha2 : 2 <= fourBridgeOneCoeff G J hf w x y z) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_two_le_oneCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz ha2


-- created on 2026-10-23
