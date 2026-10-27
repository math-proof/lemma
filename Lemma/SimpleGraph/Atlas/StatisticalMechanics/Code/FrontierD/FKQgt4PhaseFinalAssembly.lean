import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4PhaseFinalAssembly
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkQgt4_discontinuity_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PhaseFinalAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_winding hq hwind

/--
[fkQgt4_critical_potts_phases_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PhaseFinalAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_potts_phases_of_winding_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit (by exact_mod_cast hq : (4 : Real) < q) / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q → ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat → Nat) (phiWired : Fin q → Nat → Nat), Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (∀ b, muFree ≠ muWired b) ∧ ∀ b c, b ≠ c → muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_potts_phases_of_winding q hq J hJ hwind

/--
[fkQgt4_critical_ergodic_potts_phases_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4PhaseFinalAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_ergodic_potts_phases_of_winding_eq
  {q : Nat}
  [NeZero q]
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit (by exact_mod_cast hq : (4 : Real) < q) / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)), IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_ergodic_potts_phases_of_winding q hq hwind


-- created on 2026-10-23
