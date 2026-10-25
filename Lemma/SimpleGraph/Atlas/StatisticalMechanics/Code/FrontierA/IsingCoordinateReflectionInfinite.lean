import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionInfinite
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {x : Site d}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 1 <= n)
  (hxi : x i = (n : Int)) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (n : Int)) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq i beta hbeta x n hn hxi

/--
[currentContinuityFreeTwoPoint_le_axis_of_natAbs_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_le_axis_of_natAbs_coordinate_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {x : Site d}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 1 <= n)
  (hxi : (x i).natAbs = n) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (n : Int)) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_le_axis_of_natAbs_coordinate i beta hbeta x n hn hxi

/--
[currentContinuityFreeTwoPoint_shell_le_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_shell_le_axis_eq
  {d : Nat}
  {beta : Real}
  {n : Nat}
  {x : Site d}
-- given
  (hd : 1 <= d)
  (hbeta : 0 <= beta)
  (hn : 1 <= n)
  (hx : x ∈ boxSV_vbF d n) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) (criticalAxisSite hd n) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_shell_le_axis hd beta hbeta n hn x hx


-- created on 2026-10-23
