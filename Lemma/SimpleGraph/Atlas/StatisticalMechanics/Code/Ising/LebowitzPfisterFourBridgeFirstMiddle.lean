import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeFirstMiddle
open StatMech StatMech.Ising


/--
[fourBridge_bernsteinOne_nonpos_of_oneCoeff_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma fourBridge_bernsteinOne_nonpos_of_oneCoeff_le_two_eq
  {a b c d : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b)
  (hc0 : 0 <= c)
  (hd0 : 0 <= d)
  (ha2 : a <= 2)
  (hzero : a ^ 3 - 3 * a * b - a + 3 * c <= 0)
  (hdis : 0 <= 1 - a + b - c + d) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b c d 1 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridge_bernsteinOne_nonpos_of_oneCoeff_le_two ha0 hb0 hc0 hd0 ha2 hzero hdis

/--
[fourBridge_bernsteinOne_nonpos_of_two_le_oneCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma fourBridge_bernsteinOne_nonpos_of_two_le_oneCoeff_eq
  {a b c d : Real}
-- given
  (ha2 : 2 <= a)
  (hp0 : 0 <= fourBridgeRankMass a b c d 0)
  (hp1 : 0 <= fourBridgeRankMass a b c d 1)
  (hp2 : 0 <= fourBridgeRankMass a b c d 2) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b c d 1 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridge_bernsteinOne_nonpos_of_two_le_oneCoeff ha2 hp0 hp1 hp2

/--
[fourBridgeAgreementSpinMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma fourBridgeAgreementSpinMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {s : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= fourBridgeAgreementSpinMass G J hf w x y z s := by
-- proof
  apply StatMech.Ising.fourBridgeAgreementSpinMass_nonneg G J hf w x y z s

/--
[fourBridgeVarianceSkewBernsteinCoeff_one_nonpos_of_oneCoeff_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_one_nonpos_of_oneCoeff_le_two_eq
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
  (hone : fourBridgeOneCoeff G J hf w x y z <= 2) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_one_nonpos_of_oneCoeff_le_two G J hf hJ hhf hwx hwy hwz hxy hxz hyz hone

/--
[fourBridgeVarianceSkewBernsteinCoeff_one_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_one_nonpos_eq
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
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_one_nonpos G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_two_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_two_four_eq
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
  (hmiddle : forall i : Fin 7, 2 <= i.val -> i.val <= 4 -> fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0) :
-- imply
  forall i, fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_two_four G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle

/--
[replicaBridgeVariance_fourBridgeSites_le_neg_of_middle_two_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma replicaBridgeVariance_fourBridgeSites_le_neg_of_middle_two_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
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
  (hmiddle : forall i : Fin 7, 2 <= i.val -> i.val <= 4 -> fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0)
  (hr : 0 <= r) :
-- imply
  replicaBridgeVariance G J hf (fourBridgeSites w x y z) r <= replicaBridgeVariance G J hf (fourBridgeSites w x y z) (-r) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_fourBridgeSites_le_neg_of_middle_two_four G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle r hr

/--
[replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle_two_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeFirstMiddle.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle_two_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
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
  (hmiddle : forall i : Fin 7, 2 <= i.val -> i.val <= 4 -> fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0)
  (hr : 0 <= r) :
-- imply
  replicaBridgeFreeEnergy G J hf (fourBridgeSites w x y z) r <= 2 * r * fourBridgeOneCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle_two_four G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle r hr


-- created on 2026-10-23
