import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTripleBranchSelection
open Filter Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[tendsto_three_max_one_fixedBranches_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTripleBranchSelection.lean)
-/
@[path]
private lemma tendsto_three_max_one_fixedBranches_subsequence_eq
-- given
  (H0 H1 V0 V1 K0 K1 : Nat -> Real)
  (hH : Tendsto (fun n => max (H0 n) (H1 n)) atTop (nhds 1))
  (hV : Tendsto (fun n => max (V0 n) (V1 n)) atTop (nhds 1))
  (hK : Tendsto (fun n => max (K0 n) (K1 n)) atTop (nhds 1)) :
-- imply
  exists phi : Nat -> Nat, StrictMono phi /\ exists hBranch vBranch kBranch : Bool, Tendsto (fun n => if hBranch then H1 (phi n) else H0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => if vBranch then V1 (phi n) else V0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => if kBranch then K1 (phi n) else K0 (phi n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.tendsto_three_max_one_fixedBranches_subsequence H0 H1 V0 V1 K0 K1 hH hV hK

/--
[NormalTwoRotatedEndpointLimitData.exists_fixedBranchesSubsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTripleBranchSelection.lean)
-/
@[path]
private lemma exists_fixedBranchesSubsequence_eq
  [DecidableEq V]
  [DecidableEq W]
  [Countable V]
  [Countable W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : MeasureTheory.Measure (ConfigSpace (Sym2 V))}
  {muDual : MeasureTheory.Measure (ConfigSpace (Sym2 W))}
  [MeasureTheory.IsProbabilityMeasure muDual]
  {data : NormalTwoRotatedEndpointLimitData E Edual mu muDual} :
-- imply
  let primalH : Nat -> Real := fun n => mu.real (E.horizontalCrossingEvent 0 (data.level n).normalX 0 (data.level n).normalY) let primalV : Nat -> Real := fun n => mu.real (E.verticalCrossingEvent (data.level n).normal.raw.data.wideLeft (data.level n).normal.raw.data.wideRight 0 (data.level n).normalY) let dualVertical0 : Nat -> Real := fun n => muDual.real (Edual.verticalCrossingEvent 0 (data.level n).normalX 0 (data.level n).normalY) let dualHorizontal0 : Nat -> Real := fun n => muDual.real (Edual.horizontalCrossingEvent 0 (data.level n).normalX (data.rotatedVerticalLevel n).raw.data.wideLeft (data.rotatedVerticalLevel n).raw.data.wideRight) let dualVertical1 : Nat -> Real := fun n => muDual.real (Edual.verticalCrossingEvent 0 (data.level n).rotatedHorizontalY 0 (data.level n).rotatedHorizontalX) let dualHorizontal1 : Nat -> Real := fun n => muDual.real (Edual.horizontalCrossingEvent 0 (data.level n).rotatedHorizontalY (data.rotatedHorizontalLevel n).raw.data.wideLeft (data.rotatedHorizontalLevel n).raw.data.wideRight) exists phi : Nat -> Nat, StrictMono phi /\ exists primalBranch dualBranch0 dualBranch1 : Bool, Tendsto (fun n => if primalBranch then primalV (phi n) else primalH (phi n)) atTop (nhds 1) /\ Tendsto (fun n => if dualBranch0 then dualHorizontal0 (phi n) else dualVertical0 (phi n)) atTop (nhds 1) /\ Tendsto (fun n => if dualBranch1 then dualHorizontal1 (phi n) else dualVertical1 (phi n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.NormalTwoRotatedEndpointLimitData.exists_fixedBranchesSubsequence data


-- created on 2026-10-23
