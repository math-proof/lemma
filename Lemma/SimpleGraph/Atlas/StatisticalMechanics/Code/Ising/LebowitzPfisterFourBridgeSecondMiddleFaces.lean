import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleFaces
open StatMech StatMech.Ising


/--
[fourBridge_bernsteinTwo_nonpos_of_enclosingFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleFaces.lean)
-/
@[path]
private lemma fourBridge_bernsteinTwo_nonpos_of_enclosingFaces_eq
  {a b c d L U : Real}
-- given
  (ha0 : 0 <= a)
  (hLU : L <= U)
  (hLc : L <= c)
  (hcU : c <= U)
  (hL : 0 <= fourBridgeSecondMiddleNumerator a b L d)
  (hU : 0 <= fourBridgeSecondMiddleNumerator a b U d) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b c d 2 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridge_bernsteinTwo_nonpos_of_enclosingFaces ha0 hLU hLc hcU hL hU

/--
[fourBridge_bernsteinTwo_nonpos_at_productFace_of_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleFaces.lean)
-/
@[path]
private lemma fourBridge_bernsteinTwo_nonpos_at_productFace_of_le_two_eq
  {a b d : Real}
-- given
  (ha0 : 0 <= a)
  (ha2 : a <= 2)
  (hb0 : 0 <= b)
  (hb6 : b <= 6)
  (hd0 : 0 <= d)
  (hd1 : d <= 1)
  (hp0 : a * (1 + d) <= b + d + 1) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b (a * d) d 2 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridge_bernsteinTwo_nonpos_at_productFace_of_le_two ha0 ha2 hb0 hb6 hd0 hd1 hp0

/--
[fourBridgeSecondMiddleNumerator_productFace_nonneg_of_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleFaces.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_productFace_nonneg_of_le_two_eq
  {a b d : Real}
-- given
  (ha0 : 0 <= a)
  (ha2 : a <= 2)
  (hb0 : 0 <= b)
  (hb6 : b <= 6)
  (hd0 : 0 <= d)
  (hd1 : d <= 1)
  (hp0 : a * (1 + d) <= b + d + 1) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b (a * d) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_productFace_nonneg_of_le_two ha0 ha2 hb0 hb6 hd0 hd1 hp0

/--
[fourBridge_bernsteinTwo_nonpos_at_rankFace_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleFaces.lean)
-/
@[path]
private lemma fourBridge_bernsteinTwo_nonpos_at_rankFace_of_two_le_eq
  {a b d : Real}
-- given
  (ha2 : 2 <= a)
  (ha4 : a <= 4)
  (hb0 : 0 <= b)
  (hb6 : b <= 6)
  (hd0 : 0 <= d)
  (hd1 : d <= 1)
  (hp0 : 2 * a + d <= b + 3)
  (hpair : 3 * a <= 6 + b) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b (a + 2 * d - 2) d 2 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridge_bernsteinTwo_nonpos_at_rankFace_of_two_le ha2 ha4 hb0 hb6 hd0 hd1 hp0 hpair

/--
[fourBridgeSecondMiddleNumerator_rankFace_nonneg_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleFaces.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleNumerator_rankFace_nonneg_of_two_le_eq
  {a b d : Real}
-- given
  (ha2 : 2 <= a)
  (ha4 : a <= 4)
  (hb0 : 0 <= b)
  (hb6 : b <= 6)
  (hd0 : 0 <= d)
  (hd1 : d <= 1)
  (hp0 : 2 * a + d <= b + 3)
  (hpair : 3 * a <= 6 + b) :
-- imply
  0 <= fourBridgeSecondMiddleNumerator a b (a + 2 * d - 2) d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleNumerator_rankFace_nonneg_of_two_le ha2 ha4 hb0 hb6 hd0 hd1 hp0 hpair


-- created on 2026-10-23
