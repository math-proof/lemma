import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeMomentBounds
open Finset SimpleGraph StatMech StatMech.Ising


/--
[fourBridge_three_sqsum_le_six_add_pairSqsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMomentBounds.lean)
-/
@[path]
private lemma fourBridge_three_sqsum_le_six_add_pairSqsum_eq
  {w x y z wx wy wz xy xz yz : Real}
-- given
  (hw0 : 0 <= w)
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hw1 : w <= 1)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (hwx : w * x <= wx)
  (hwy : w * y <= wy)
  (hwz : w * z <= wz)
  (hxy : x * y <= xy)
  (hxz : x * z <= xz)
  (hyz : y * z <= yz) :
-- imply
  3 * (w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) <= 6 + (wx ^ 2 + wy ^ 2 + wz ^ 2 + xy ^ 2 + xz ^ 2 + yz ^ 2) := by
-- proof
  apply StatMech.Ising.fourBridge_three_sqsum_le_six_add_pairSqsum hw0 hx0 hy0 hz0 hw1 hx1 hy1 hz1 hwx hwy hwz hxy hxz hyz

/--
[fourBridgeOneCoeff_three_mul_le_six_add_twoCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMomentBounds.lean)
-/
@[path]
private lemma fourBridgeOneCoeff_three_mul_le_six_add_twoCoeff_eq
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
  3 * fourBridgeOneCoeff G J hf w x y z <= 6 + fourBridgeTwoCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridgeOneCoeff_three_mul_le_six_add_twoCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridgeThreeCoeff_three_mul_le_six_add_twoCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMomentBounds.lean)
-/
@[path]
private lemma fourBridgeThreeCoeff_three_mul_le_six_add_twoCoeff_eq
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
  3 * fourBridgeThreeCoeff G J hf w x y z <= 6 + fourBridgeTwoCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridgeThreeCoeff_three_mul_le_six_add_twoCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz

/--
[fourBridge_pairSqsum_sq_le_five_mul_add_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMomentBounds.lean)
-/
@[path]
private lemma fourBridge_pairSqsum_sq_le_five_mul_add_six_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d e f r : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b)
  (hc0 : 0 <= c)
  (hd0 : 0 <= d)
  (he0 : 0 <= e)
  (hf0 : 0 <= f)
  (ha1 : a <= 1)
  (hb1 : b <= 1)
  (hc1 : c <= 1)
  (hd1 : d <= 1)
  (he1 : e <= 1)
  (hf1 : f <= 1)
  (hab : a * b <= d)
  (hac : a * c <= e)
  (had : a * d <= b)
  (hae : a * e <= c)
  (hbc : b * c <= f)
  (hbd : b * d <= a)
  (hbf : b * f <= c)
  (hce : c * e <= a)
  (hcf : c * f <= b)
  (hde : d * e <= f)
  (hdf : d * f <= e)
  (hef : e * f <= d)
  (haf : a * f <= r)
  (hbe : b * e <= r)
  (hcd : c * d <= r) :
-- imply
  (a + b + c + d + e + f) ^ 2 <= 5 * (a + b + c + d + e + f) + 6 * r := by
-- proof
  apply StatMech.Ising.fourBridge_pairSqsum_sq_le_five_mul_add_six ha0 hb0 hc0 hd0 he0 hf0 ha1 hb1 hc1 hd1 he1 hf1 hab hac had hae hbc hbd hbf hce hcf hde hdf hef haf hbe hcd

/--
[fourBridgeTwoCoeff_sq_le_five_mul_add_six_fourCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeMomentBounds.lean)
-/
@[path]
private lemma fourBridgeTwoCoeff_sq_le_five_mul_add_six_fourCoeff_eq
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
  fourBridgeTwoCoeff G J hf w x y z ^ 2 <= 5 * fourBridgeTwoCoeff G J hf w x y z + 6 * fourBridgeFourCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridgeTwoCoeff_sq_le_five_mul_add_six_fourCoeff G J hf hJ hhf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
