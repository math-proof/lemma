import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionSandwich
open StatMech StatMech.FrontierA


/--
[quantumIsingNormalizedDiagonalPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionSandwich.lean)
-/
@[path]
private lemma quantumIsingNormalizedDiagonalPartition_pos_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real) :
-- imply
  0 < quantumIsingNormalizedDiagonalPartition beta h L := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedDiagonalPartition_pos beta h L

/--
[quantumIsingNormalizedSpinSector_norm_le_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionSandwich.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_norm_le_partition_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  ‖quantumIsingNormalizedSpinSector beta h L a b‖ ≤ quantumIsingNormalizedDiagonalPartition beta h L := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_norm_le_partition beta h L hbeta hx hx1 a b

/--
[quantumIsingNormalizedDiagonalPartition_log_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionSandwich.lean)
-/
@[path]
private lemma quantumIsingNormalizedDiagonalPartition_log_sandwich_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  Real.log (arfSectorNormMax (quantumIsingNormalizedSpinSector beta h L)) ≤ Real.log (quantumIsingNormalizedDiagonalPartition beta h L) ∧ Real.log (quantumIsingNormalizedDiagonalPartition beta h L) ≤ Real.log (arfSectorNormMax (quantumIsingNormalizedSpinSector beta h L)) + Real.log 2 := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedDiagonalPartition_log_sandwich beta h L hbeta hx hx1


-- created on 2026-10-23
