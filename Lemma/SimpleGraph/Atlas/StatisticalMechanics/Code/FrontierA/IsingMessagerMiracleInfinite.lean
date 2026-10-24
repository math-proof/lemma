import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingMessagerMiracleInfinite
open Finset StatMech StatMech.FrontierA


/--
[currentContinuityFreeTwoPoint_axis_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingMessagerMiracleInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_succ_le_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {n : Nat}
-- given
  (hd : 2 <= d)
  (hbeta : 0 <= beta)
  (hn : 1 <= n) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i ((n + 1 : Nat) : Int)) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (n : Int)) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_succ_le hd i beta hbeta n hn

/--
[currentContinuityFreeTwoPoint_axis_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingMessagerMiracleInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_axis_antitone_eq
  {d : Nat}
  {i : Fin d}
  {beta : Real}
  {p q : Nat}
-- given
  (hd : 2 <= d)
  (hbeta : 0 <= beta)
  (hp : 1 <= p)
  (hpq : p <= q) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (q : Int)) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) (Pi.single i (p : Int)) := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_axis_antitone hd i beta hbeta p q hp hpq

/--
[criticalIsingMessagerMiracle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingMessagerMiracleInfinite.lean)
-/
@[path]
private lemma criticalIsingMessagerMiracle_eq
  {d : Nat}
  {d : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  CriticalIsingMessagerMiracle d (by omega) := by
-- proof
  apply StatMech.FrontierA.criticalIsingMessagerMiracle d hd

/--
[criticalBoundaryTwoPoint_powerLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingMessagerMiracleInfinite.lean)
-/
@[path]
private lemma criticalBoundaryTwoPoint_powerLower_eq
  {d : Nat}
  {d n : Nat}
  {x : Site d}
-- given
  (hd : 2 <= d)
  (hn : 1 <= n)
  (hx : x ∈ boxSV_vbF d n) :
-- imply
  1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) * (2 * ((d * n : Nat) : Real) + 1) ^ (d - 1)) <= currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.criticalBoundaryTwoPoint_powerLower hd hn x hx


-- created on 2026-10-23
