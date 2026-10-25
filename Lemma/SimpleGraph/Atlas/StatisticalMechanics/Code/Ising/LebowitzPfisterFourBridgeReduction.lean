import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeReduction
open StatMech StatMech.Ising


/--
[fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeReduction.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle_eq
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
  (hcoeffOne : fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 <= 0)
  (hcoeffTwo : fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 <= 0)
  (hcoeffThree : fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 3 <= 0)
  (hcoeffFour : fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4 <= 0) :
-- imply
  forall i, fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_all_nonpos_of_middle G J hf hJ hhf hwx hwy hwz hxy hxz hyz hcoeffOne hcoeffTwo hcoeffThree hcoeffFour

/--
[replicaBridgeVariance_fourBridgeSites_le_neg_of_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeReduction.lean)
-/
@[path]
private lemma replicaBridgeVariance_fourBridgeSites_le_neg_of_middle_eq
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
  (hmiddle : forall i : Fin 7, 1 <= i.val -> i.val <= 4 -> fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0)
  (hr : 0 <= r) :
-- imply
  replicaBridgeVariance G J hf (fourBridgeSites w x y z) r <= replicaBridgeVariance G J hf (fourBridgeSites w x y z) (-r) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_fourBridgeSites_le_neg_of_middle G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle r hr

/--
[replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeReduction.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle_eq
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
  (hmiddle : forall i : Fin 7, 1 <= i.val -> i.val <= 4 -> fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) i <= 0)
  (hr : 0 <= r) :
-- imply
  replicaBridgeFreeEnergy G J hf (fourBridgeSites w x y z) r <= 2 * r * fourBridgeOneCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_fourBridgeSites_le_of_middle G J hf hJ hhf hwx hwy hwz hxy hxz hyz hmiddle r hr


-- created on 2026-10-23
