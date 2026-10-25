/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/RectangularPrismTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
import Theorem.StatisticalMechanics.Code.Ising.CenterMarkedPath.Part2
import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferCenterObservable
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part2
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

def rectangularLayerInternalInteraction {m n : Nat}
    (s : RectangularLayerConfig m n) : Real :=
  (∑ x : Fin (m - 1), ∑ y : Fin n,
      spin s (⟨x.val, by omega⟩, y) *
        spin s (⟨x.val + 1, by omega⟩, y)) +
    ∑ x : Fin m, ∑ y : Fin (n - 1),
      spin s (x, ⟨y.val, by omega⟩) *
        spin s (x, ⟨y.val + 1, by omega⟩)


def rectangularLayerBoundaryDegree {m n : Nat} (p : Fin m × Fin n) : Nat :=
  (if p.1.val = 0 then 1 else 0) +
  (if p.1.val + 1 = m then 1 else 0) +
  (if p.2.val = 0 then 1 else 0) +
  (if p.2.val + 1 = n then 1 else 0)


def rectangularLayerBoltzmannInteraction (J beta : Real) {m n : Nat}
    (s : RectangularLayerConfig m n) : Real :=
  beta * J * (rectangularLayerInternalInteraction s +
    ∑ p : Fin m × Fin n,
      rectangularLayerBoundaryDegree p * spin s p)


def rectangularLayerVerticalInteraction (J beta : Real) {m n : Nat}
    (s t : RectangularLayerConfig m n) : Real :=
  beta * J * ∑ p : Fin m × Fin n, spin s p * spin t p


def rectangularLayerFaceBoundary (J beta : Real) {m n : Nat}
    (s : RectangularLayerConfig m n) : Real :=
  beta * J * ∑ p : Fin m × Fin n, spin s p

end
end StatMech.Ising
