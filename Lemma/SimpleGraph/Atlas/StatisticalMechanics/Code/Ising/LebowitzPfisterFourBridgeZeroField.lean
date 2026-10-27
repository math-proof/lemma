import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeZeroField
open StatMech StatMech.Ising


/--
[fourBridgeOneCoeff_zeroField_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeZeroField.lean)
-/
@[path]
private lemma fourBridgeOneCoeff_zeroField_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  fourBridgeOneCoeff G J (fun _ => 0) w x y z = 0 := by
-- proof
  apply StatMech.Ising.fourBridgeOneCoeff_zeroField_eq_zero G J w x y z

/--
[fourBridgeThreeCoeff_zeroField_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeZeroField.lean)
-/
@[path]
private lemma fourBridgeThreeCoeff_zeroField_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeThreeCoeff G J (fun _ => 0) w x y z = 0 := by
-- proof
  apply StatMech.Ising.fourBridgeThreeCoeff_zeroField_eq_zero G J w x y z hwx hwy hwz hxy hxz hyz

/--
[fourBridgeRankMass_rankCross_zeroField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeZeroField.lean)
-/
@[path]
private lemma fourBridgeRankMass_rankCross_zeroField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  let a := fourBridgeOneCoeff G J (fun _ => 0) w x y z let b := fourBridgeTwoCoeff G J (fun _ => 0) w x y z let c := fourBridgeThreeCoeff G J (fun _ => 0) w x y z let d := fourBridgeFourCoeff G J (fun _ => 0) w x y z fourBridgeRankMass a b c d 0 * fourBridgeRankMass a b c d 3 = fourBridgeRankMass a b c d 1 * fourBridgeRankMass a b c d 4 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_rankCross_zeroField G J w x y z hwx hwy hwz hxy hxz hyz

/--
[fourBridgeVarianceSkewBernsteinCoeff_five_six_zeroField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeZeroField.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_five_six_zeroField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  let a := fourBridgeOneCoeff G J (fun _ => 0) w x y z let b := fourBridgeTwoCoeff G J (fun _ => 0) w x y z let c := fourBridgeThreeCoeff G J (fun _ => 0) w x y z let d := fourBridgeFourCoeff G J (fun _ => 0) w x y z fourBridgeVarianceSkewBernsteinCoeff a b c d 5 = 0 /\ fourBridgeVarianceSkewBernsteinCoeff a b c d 6 = 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_five_six_zeroField G J w x y z hwx hwy hwz hxy hxz hyz

/--
[fourBridgeVarianceSkewBernsteinCoeff_all_zeroField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeZeroField.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_all_zeroField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  let a := fourBridgeOneCoeff G J (fun _ => 0) w x y z let b := fourBridgeTwoCoeff G J (fun _ => 0) w x y z let c := fourBridgeThreeCoeff G J (fun _ => 0) w x y z let d := fourBridgeFourCoeff G J (fun _ => 0) w x y z ∀ i : Fin 7, fourBridgeVarianceSkewBernsteinCoeff a b c d i = 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_all_zeroField G J w x y z hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
