import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeProductBounds
open Finset SimpleGraph StatMech StatMech.Ising


/--
[expJ_spinProd_sq_mul_sq_le_symmDiff_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma expJ_spinProd_sq_mul_sq_le_symmDiff_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A B : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v) :
-- imply
  (expJ G.edgeFinset J hf (spinProd A)) ^ 2 * (expJ G.edgeFinset J hf (spinProd B)) ^ 2 <= (expJ G.edgeFinset J hf (spinProd (A ∆ B))) ^ 2 := by
-- proof
  apply StatMech.Ising.expJ_spinProd_sq_mul_sq_le_symmDiff_sq G J hf hJ hhf A B

/--
[fourBridgeOneCoeff_mul_fourCoeff_le_threeCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridgeOneCoeff_mul_fourCoeff_le_threeCoeff_eq
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
  fourBridgeOneCoeff G J hf w x y z * fourBridgeFourCoeff G J hf w x y z <= fourBridgeThreeCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridgeOneCoeff_mul_fourCoeff_le_threeCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeThreeCoeff_mul_fourCoeff_le_oneCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridgeThreeCoeff_mul_fourCoeff_le_oneCoeff_eq
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
  fourBridgeThreeCoeff G J hf w x y z * fourBridgeFourCoeff G J hf w x y z <= fourBridgeOneCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridgeThreeCoeff_mul_fourCoeff_le_oneCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridge_four_by_four_product_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridge_four_by_four_product_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {u0 u1 u2 u3 t0 t1 t2 t3 p01 p02 p03 p12 p13 p23 r : Real}
-- given
  (h00 : u0 * t0 <= r)
  (h11 : u1 * t1 <= r)
  (h22 : u2 * t2 <= r)
  (h33 : u3 * t3 <= r)
  (h01 : u0 * t1 <= p23)
  (h02 : u0 * t2 <= p13)
  (h03 : u0 * t3 <= p12)
  (h10 : u1 * t0 <= p23)
  (h12 : u1 * t2 <= p03)
  (h13 : u1 * t3 <= p02)
  (h20 : u2 * t0 <= p13)
  (h21 : u2 * t1 <= p03)
  (h23 : u2 * t3 <= p01)
  (h30 : u3 * t0 <= p12)
  (h31 : u3 * t1 <= p02)
  (h32 : u3 * t2 <= p01) :
-- imply
  (u0 + u1 + u2 + u3) * (t0 + t1 + t2 + t3) <= 2 * (p01 + p02 + p03 + p12 + p13 + p23) + 4 * r := by
-- proof
  apply StatMech.Ising.fourBridge_four_by_four_product_sum_le h00 h11 h22 h33 h01 h02 h03 h10 h12 h13 h20 h21 h23 h30 h31 h32

/--
[fourBridge_four_by_six_product_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridge_four_by_six_product_sum_le_eq
  [Fintype V]
  [DecidableEq V]
  {u0 u1 u2 u3 p01 p02 p03 p12 p13 p23 t0 t1 t2 t3 : Real}
-- given
  (h001 : u0 * p01 <= u1)
  (h002 : u0 * p02 <= u2)
  (h003 : u0 * p03 <= u3)
  (h012 : u0 * p12 <= t3)
  (h013 : u0 * p13 <= t2)
  (h023 : u0 * p23 <= t1)
  (h101 : u1 * p01 <= u0)
  (h102 : u1 * p02 <= t3)
  (h103 : u1 * p03 <= t2)
  (h112 : u1 * p12 <= u2)
  (h113 : u1 * p13 <= u3)
  (h123 : u1 * p23 <= t0)
  (h201 : u2 * p01 <= t3)
  (h202 : u2 * p02 <= u0)
  (h203 : u2 * p03 <= t1)
  (h212 : u2 * p12 <= u1)
  (h213 : u2 * p13 <= t0)
  (h223 : u2 * p23 <= u3)
  (h301 : u3 * p01 <= t2)
  (h302 : u3 * p02 <= t1)
  (h303 : u3 * p03 <= u0)
  (h312 : u3 * p12 <= t0)
  (h313 : u3 * p13 <= u1)
  (h323 : u3 * p23 <= u2) :
-- imply
  (u0 + u1 + u2 + u3) * (p01 + p02 + p03 + p12 + p13 + p23) <= 3 * ((u0 + u1 + u2 + u3) + (t0 + t1 + t2 + t3)) := by
-- proof
  apply StatMech.Ising.fourBridge_four_by_six_product_sum_le h001 h002 h003 h012 h013 h023 h101 h102 h103 h112 h113 h123 h201 h202 h203 h212 h213 h223 h301 h302 h303 h312 h313 h323

/--
[fourBridgeOneCoeff_mul_threeCoeff_le_two_mul_twoCoeff_add_four_mul_fourCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridgeOneCoeff_mul_threeCoeff_le_two_mul_twoCoeff_add_four_mul_fourCoeff_eq
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
  fourBridgeOneCoeff G J hf w x y z * fourBridgeThreeCoeff G J hf w x y z <= 2 * fourBridgeTwoCoeff G J hf w x y z + 4 * fourBridgeFourCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridgeOneCoeff_mul_threeCoeff_le_two_mul_twoCoeff_add_four_mul_fourCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeOneCoeff_mul_twoCoeff_le_three_mul_one_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridgeOneCoeff_mul_twoCoeff_le_three_mul_one_add_three_eq
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
  fourBridgeOneCoeff G J hf w x y z * fourBridgeTwoCoeff G J hf w x y z <= 3 * (fourBridgeOneCoeff G J hf w x y z + fourBridgeThreeCoeff G J hf w x y z) := by
-- proof
  apply StatMech.Ising.fourBridgeOneCoeff_mul_twoCoeff_le_three_mul_one_add_three G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeTwoCoeff_mul_threeCoeff_le_three_mul_one_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeProductBounds.lean)
-/
@[path]
private lemma fourBridgeTwoCoeff_mul_threeCoeff_le_three_mul_one_add_three_eq
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
  fourBridgeTwoCoeff G J hf w x y z * fourBridgeThreeCoeff G J hf w x y z <= 3 * (fourBridgeOneCoeff G J hf w x y z + fourBridgeThreeCoeff G J hf w x y z) := by
-- proof
  apply StatMech.Ising.fourBridgeTwoCoeff_mul_threeCoeff_le_three_mul_one_add_three G J hf hJ hhf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
