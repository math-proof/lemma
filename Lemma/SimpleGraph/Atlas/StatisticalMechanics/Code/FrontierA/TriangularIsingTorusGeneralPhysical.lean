import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGeneralPhysical
open StatMech StatMech.FrontierA


/--
[triangularTorusIsingPartition_freeEnergy_first_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGeneralPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_first_lipschitz_eq
  {J1 K1 J2 J3 : Real}
  {n : Nat} :
-- imply
  |(-Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) / (n + 3 : Real) ^ 2) - (-Real.log (triangularTorusIsingPartitionSequence K1 J2 J3 n) / (n + 3 : Real) ^ 2)| ≤ |J1 - K1| := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_first_lipschitz J1 K1 J2 J3 n

/--
[triangularTorusIsingPartition_freeEnergy_tendsto_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGeneralPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_general_eq
  {J1 J2 J3 : Real} :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto_general J1 J2 J3


-- created on 2026-10-23
