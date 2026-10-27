import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointShell.Part3
open Finset MeasureTheory Set StatMech StatMech.FrontierA


/--
[isingExpectation_instance_irrel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma isingExpectation_instance_irrel_eq
  {i j : Fintype V}
  {deqI deqJ : DecidableEq V}
  {G : SimpleGraph V}
  {adjI adjJ : DecidableRel G.Adj}
  {f : ConfigSpace V → Real}
-- given
  (beta h : Real) :
-- imply
  @isingExpectation V i deqI G adjI beta h f = @isingExpectation V j deqJ G adjJ beta h f := by
-- proof
  apply StatMech.FrontierA.isingExpectation_instance_irrel i j deqI deqJ G adjI adjJ beta h f

/--
[corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint_eq
  {d n : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hx : x ∈ box d n)
  (hxo : x ≠ Percolation.origin d) :
-- imply
  corrOriginInner d beta (boxSV_boxF d n) x = currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint d n beta x hx hxo

/--
[corrOriginInner_box_le_currentContinuityFreeTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma corrOriginInner_box_le_currentContinuityFreeTwoPoint_eq
  {d n : Nat}
  {beta : Real}
  {x : Site d}
-- given
  (hbeta : 0 ≤ beta)
  (hx : x ∈ box d n)
  (hxo : x ≠ Percolation.origin d) :
-- imply
  corrOriginInner d beta (boxSV_boxF d n) x ≤ currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.corrOriginInner_box_le_currentContinuityFreeTwoPoint d n beta hbeta x hx hxo

/--
[criticalAxisSite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma criticalAxisSite_mem_box_eq
  {d n : Nat}
-- given
  (hd : 1 ≤ d) :
-- imply
  criticalAxisSite hd n ∈ box d n := by
-- proof
  apply StatMech.FrontierA.criticalAxisSite_mem_box hd

/--
[criticalAxisSite_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma criticalAxisSite_ne_origin_eq
  {d n : Nat}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n) :
-- imply
  criticalAxisSite hd n ≠ Percolation.origin d := by
-- proof
  apply StatMech.FrontierA.criticalAxisSite_ne_origin hd hn

/--
[criticalAxisTwoPoint_powerLower_of_shellComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma criticalAxisTwoPoint_powerLower_of_shellComparison_eq
  {d n : Nat}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hshell : ∀ e ∈ boundaryEdges d (boxSV_boxF d n), currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) e.1 ≤ currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) (criticalAxisSite (by omega) n)) :
-- imply
  1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) * (2 * (n : Real) + 1) ^ (d - 1)) ≤ currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) (criticalAxisSite (by omega) n) := by
-- proof
  apply StatMech.FrontierA.criticalAxisTwoPoint_powerLower_of_shellComparison hd hn hshell

/--
[criticalBoundaryTwoPoint_powerLower_of_messagerMiracle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean)
-/
@[path]
private lemma criticalBoundaryTwoPoint_powerLower_of_messagerMiracle_eq
  {d n : Nat}
  {x : Site d}
-- given
  (hd : 2 ≤ d)
  (hn : 1 ≤ n)
  (hMM : CriticalIsingMessagerMiracle d (by omega))
  (hx : x ∈ boxSV_vbF d n) :
-- imply
  1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) * (2 * ((d * n : Nat) : Real) + 1) ^ (d - 1)) ≤ currentContinuityFreeTwoPoint d (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.criticalBoundaryTwoPoint_powerLower_of_messagerMiracle hd hn hMM x hx


-- created on 2026-10-23
