/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part10


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialCellRegionBoundaryIntegral
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (cells : Finset (Nat × Nat)) : Complex :=
  ∑ p ∈ cells, reflectedRadialBilinearCellContour mesh
    (F p.1 p.2) (F (p.1 + 1) p.2)
    (F p.1 (p.2 + 1)) (F (p.1 + 1) (p.2 + 1))


end
end StatMech.Universality
