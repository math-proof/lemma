import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFieldGauge.Part2
open Matrix StatMech StatMech.FrontierA


/--
[quantumIsingFieldGaugeSign_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean)
-/
@[path]
private lemma quantumIsingFieldGaugeSign_sq_eq
  {L : Nat}
  {sigma : QuantumIsingChainConfig L} :
-- imply
  quantumIsingFieldGaugeSign sigma * quantumIsingFieldGaugeSign sigma = 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingFieldGaugeSign_sq sigma

/--
[quantumIsingFieldGaugeSign_eq_neg_of_disagreementCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean)
-/
@[path]
private lemma quantumIsingFieldGaugeSign_eq_neg_of_disagreementCount_eq_one_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (hcount : quantumIsingDisagreementCount sigma tau = 1) :
-- imply
  quantumIsingFieldGaugeSign sigma = -quantumIsingFieldGaugeSign tau := by
-- proof
  apply StatMech.FrontierA.quantumIsingFieldGaugeSign_eq_neg_of_disagreementCount_eq_one sigma tau hcount

/--
[quantumIsingFieldGaugeMatrix_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean)
-/
@[path]
private lemma quantumIsingFieldGaugeMatrix_sq_eq
  {L : Nat} :
-- imply
  quantumIsingFieldGaugeMatrix L * quantumIsingFieldGaugeMatrix L = 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingFieldGaugeMatrix_sq L

/--
[quantumIsingFieldGaugeMatrix_mul_hamiltonian_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean)
-/
@[path]
private lemma quantumIsingFieldGaugeMatrix_mul_hamiltonian_mul_eq
  {L : Nat}
-- given
  (h : Real) :
-- imply
  quantumIsingFieldGaugeMatrix L * quantumIsingHamiltonian h L * quantumIsingFieldGaugeMatrix L = quantumIsingHamiltonian (-h) L := by
-- proof
  apply StatMech.FrontierA.quantumIsingFieldGaugeMatrix_mul_hamiltonian_mul h L

/--
[quantumIsingFieldGaugeMatrix_mul_generator_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean)
-/
@[path]
private lemma quantumIsingFieldGaugeMatrix_mul_generator_mul_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  quantumIsingFieldGaugeMatrix L * quantumIsingBoltzmannGenerator beta h L * quantumIsingFieldGaugeMatrix L = quantumIsingBoltzmannGenerator beta (-h) L := by
-- proof
  apply StatMech.FrontierA.quantumIsingFieldGaugeMatrix_mul_generator_mul beta h L

/--
[quantumIsingQuantumPartition_neg_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFieldGauge.lean)
-/
@[path]
private lemma quantumIsingQuantumPartition_neg_field_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  quantumIsingQuantumPartition beta (-h) L = quantumIsingQuantumPartition beta h L := by
-- proof
  apply StatMech.FrontierA.quantumIsingQuantumPartition_neg_field beta h L


-- created on 2026-10-23
