/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismGinibre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
import Theorem.StatisticalMechanics.Code.Ising.PlusStateSpinProfileLimit
import Theorem.StatisticalMechanics.Code.IsingFK.MagnetizationFK
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

def oddPrismInternalEdge (n : Nat) :
    OddPrismInternalIndex n ->
      Sym2 (RectangularPrismSite (2 * n + 1) (2 * n + 1) n)
  | .inl q => s(⟨⟨q.1.val, by omega⟩, q.2.1, q.2.2⟩,
      ⟨⟨q.1.val + 1, by omega⟩, q.2.1, q.2.2⟩)
  | .inr (.inl q) => s(⟨q.1, ⟨q.2.1.val, by omega⟩, q.2.2⟩,
      ⟨q.1, ⟨q.2.1.val + 1, by omega⟩, q.2.2⟩)
  | .inr (.inr q) => s(⟨q.1, q.2.1, ⟨q.2.2.val, by omega⟩⟩,
      ⟨q.1, q.2.1, ⟨q.2.2.val + 1, by omega⟩⟩)


def oddPrismInternalIndexToTouch (n : Nat) :
    OddPrismInternalIndex n -> OddPrismTouchIndex n
  | .inl q => .xInternal q.1 q.2.1 q.2.2
  | .inr (.inl q) => .yInternal q.1 q.2.1 q.2.2
  | .inr (.inr q) => .zInternal q.1 q.2.1 q.2.2


def oddPrismTouchToInternal (n : Nat) :
    OddPrismTouchIndex n -> Option (OddPrismInternalIndex n)
  | .xInternal x y z => some (.inl (x, y, z))
  | .yInternal x y z => some (.inr (.inl (x, y, z)))
  | .zInternal x y z => some (.inr (.inr (x, y, z)))
  | .xZero _ _ | .xLast _ _ | .yZero _ _ | .yLast _ _ |
      .zZero _ _ | .zLast _ _ => none

end
end StatMech.FrontierA
