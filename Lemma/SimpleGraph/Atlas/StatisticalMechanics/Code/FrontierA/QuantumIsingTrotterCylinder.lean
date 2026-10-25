import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
open StatMech StatMech.FrontierA


/--
[quantumIsingCyclicSucc_eq_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingCyclicSucc_eq_add_one_eq
  {m : Nat}
  [NeZero m]
  {i : Fin m} :
-- imply
  quantumIsingCyclicSucc i = i + 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingCyclicSucc_eq_add_one i

/--
[quantumIsingTrotterTrace_eq_pathPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingTrotterTrace_eq_pathPartition_eq
  {n L : Nat}
  [NeZero n]
-- given
  (beta h : Real)
  (hn : 0 < n) :
-- imply
  ((quantumIsingTrotterTransferMatrix beta h n L) ^ n).trace = (quantumIsingTrotterPathPartition beta h n L : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTrace_eq_pathPartition beta h n L hn

/--
[quantumIsingTrotterTransferKernel_eq_classicalLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingTrotterTransferKernel_eq_classicalLayer_eq
  {n L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (beta h : Real)
  (hpos : 0 < beta * h / (2 * n)) :
-- imply
  quantumIsingTrotterTransferKernel beta h n L sigma tau = (∏ _i : Fin L, Real.exp (-quantumIsingVerticalCoupling beta h n)) * (quantumIsingSpatialTrotterWeight beta n L sigma * ∏ i : Fin L, quantumIsingVerticalBondWeight beta h n (sigma i) (tau i)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTransferKernel_eq_classicalLayer beta h n L sigma tau hpos

/--
[quantumIsingTrotterPathWeight_eq_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingTrotterPathWeight_eq_classical_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (omega : Fin n -> QuantumIsingChainConfig L)
  (hpos : 0 < beta * h / (2 * n)) :
-- imply
  (∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n L (omega k) (omega (quantumIsingCyclicSucc k))) = quantumIsingTrotterNormalization beta h n L * quantumIsingClassicalCylinderWeight beta h n L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterPathWeight_eq_classical beta h n L omega hpos

/--
[quantumIsingTrotterPathPartition_eq_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingTrotterPathPartition_eq_classical_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hpos : 0 < beta * h / (2 * n)) :
-- imply
  quantumIsingTrotterPathPartition beta h n L = quantumIsingTrotterNormalization beta h n L * quantumIsingClassicalCylinderPartition beta h n L := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterPathPartition_eq_classical beta h n L hpos

/--
[quantumIsingTrotterNormalization_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingTrotterNormalization_eq_pow_eq
  {n L : Nat}
-- given
  (beta h : Real) :
-- imply
  quantumIsingTrotterNormalization beta h n L = Real.exp (-quantumIsingVerticalCoupling beta h n) ^ (L * n) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterNormalization_eq_pow beta h n L

/--
[quantumIsingTrotterTrace_eq_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean)
-/
@[path]
private lemma quantumIsingTrotterTrace_eq_classical_eq
  {n L : Nat}
  [NeZero n]
-- given
  (beta h : Real)
  (hn : 0 < n)
  (hpos : 0 < beta * h / (2 * n)) :
-- imply
  ((quantumIsingTrotterTransferMatrix beta h n L) ^ n).trace = (Real.exp (-quantumIsingVerticalCoupling beta h n) ^ (L * n) * quantumIsingClassicalCylinderPartition beta h n L : Real) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTrace_eq_classical beta h n L hn hpos


-- created on 2026-10-23
