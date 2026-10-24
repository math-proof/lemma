import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleLowRank
open StatMech StatMech.Ising


/--
[fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_le_one_eq
  {a b d : Real}
-- given
  (ha0 : 0 <= a)
  (ha1 : a <= 1)
  (hb0 : 0 <= b)
  (hd0 : 0 <= d) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b ((a + 3 * a * b - a ^ 3) / 3) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_le_one ha0 ha1 hb0 hd0

/--
[fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_one_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_one_le_two_eq
  {a b d : Real}
-- given
  (ha1 : 1 <= a)
  (ha2 : a <= 2)
  (hd0 : 0 <= d)
  (hprod : a * d <= (a + 3 * a * b - a ^ 3) / 3)
  (hrank0 : (a + 3 * a * b - a ^ 3) / 3 <= 1 - a + b + d) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b ((a + 3 * a * b - a ^ 3) / 3) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_ghsFace_nonneg_of_one_le_two ha1 ha2 hd0 hprod hrank0

/--
[fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_one_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_one_le_two_eq
  {a b d : Real}
-- given
  (ha1 : 1 <= a)
  (ha2 : a <= 2)
  (hd0 : 0 <= d)
  (hd1 : d <= 1)
  (hprod : a * d <= 1 - a + b + d)
  (hrank3 : 1 - a + b + d <= 2 + a - 2 * d) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b (1 - a + b + d) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_rankZeroFace_nonneg_of_one_le_two ha1 ha2 hd0 hd1 hprod hrank3

/--
[fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_one_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_one_le_two_eq
  {a b d : Real}
-- given
  (ha1 : 1 <= a)
  (ha2 : a <= 2)
  (hd1 : d <= 1)
  (hrank0 : 2 + a - 2 * d <= 1 - a + b + d)
  (hp2 : b <= 3 + 3 * d) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b (2 + a - 2 * d) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_rankThreeFace_nonneg_of_one_le_two ha1 ha2 hd1 hrank0 hp2

/--
[fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_oneCoeff_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_oneCoeff_le_two_eq
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
  (ha2 : fourBridgeOneCoeff G J hf w x y z <= 2) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_of_oneCoeff_le_two G J hf hJ hhf hwx hwy hwz hxy hxz hyz ha2

/--
[fourBridgeVarianceSkewBernsteinCoeff_two_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_two_nonpos_eq
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
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_two_nonpos G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_three_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleLowRank.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_three_four_eq
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
  (hthree : fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 3 <= 0)
  (hfour : fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4 <= 0) :
-- imply
  forall i, fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_three_four G J hf hJ hhf hwx hwy hwz hxy hxz hyz hthree hfour


-- created on 2026-10-23
