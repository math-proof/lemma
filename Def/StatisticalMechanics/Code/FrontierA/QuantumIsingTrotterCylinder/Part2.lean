/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable def quantumIsingChainInteraction (L : Nat)
    (sigma : QuantumIsingChainConfig L) : Real :=
  ∑ i : Fin L,
    quantumIsingSpinSign (sigma i) *
      quantumIsingSpinSign (sigma (quantumIsingCyclicSucc i))


noncomputable def quantumIsingSpatialTrotterWeight
    (beta : Real) (n L : Nat) (sigma : QuantumIsingChainConfig L) : Real :=
  Real.exp (beta / (4 * n) * quantumIsingChainInteraction L sigma)


noncomputable def quantumIsingVerticalBondWeight
    (beta h : Real) (n : Nat) (s t : Bool) : Real :=
  Real.exp (quantumIsingVerticalCoupling beta h n *
    (quantumIsingSpinSign s * quantumIsingSpinSign t))


noncomputable def quantumIsingTrotterTransferKernel
    (beta h : Real) (n L : Nat)
    (sigma tau : QuantumIsingChainConfig L) : Real :=
  quantumIsingSpatialTrotterWeight beta n L sigma *
    ∏ i : Fin L, quantumIsingTrotterKernel beta h n (sigma i) (tau i)


noncomputable def quantumIsingTrotterTransferMatrix
    (beta h : Real) (n L : Nat) :
    Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex :=
  fun sigma tau =>
    (quantumIsingTrotterTransferKernel beta h n L sigma tau : Complex)


noncomputable def quantumIsingTrotterPathPartition
    (beta h : Real) (n L : Nat) : Real :=
  ∑ omega : Fin n -> QuantumIsingChainConfig L,
    ∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n L
      (omega k) (omega (quantumIsingCyclicSucc k))


noncomputable def quantumIsingClassicalCylinderWeight
    (beta h : Real) (n L : Nat)
    (omega : Fin n -> QuantumIsingChainConfig L) : Real :=
  ∏ k : Fin n,
    quantumIsingSpatialTrotterWeight beta n L (omega k) *
      ∏ i : Fin L, quantumIsingVerticalBondWeight beta h n
        (omega k i) (omega (quantumIsingCyclicSucc k) i)


noncomputable def quantumIsingClassicalCylinderPartition
    (beta h : Real) (n L : Nat) : Real :=
  ∑ omega : Fin n -> QuantumIsingChainConfig L,
    quantumIsingClassicalCylinderWeight beta h n L omega


noncomputable def quantumIsingTrotterNormalization
    (beta h : Real) (n L : Nat) : Real :=
  ∏ _k : Fin n, ∏ _i : Fin L,
    Real.exp (-quantumIsingVerticalCoupling beta h n)


end StatMech.FrontierA
