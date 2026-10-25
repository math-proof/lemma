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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part2
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem sum_oddPrismInternalEdges
    (n : Nat)
    (f : Sym2 (RectangularPrismSite (2 * n + 1) (2 * n + 1) n) -> Real) :
    (∑ e ∈ oddPrismInternalEdges n, f e) =
      ∑ q : OddPrismInternalIndex n, f (oddPrismInternalEdge n q) := by
  rw [oddPrismInternalEdges,
    Finset.sum_image (s := Finset.univ) (oddPrismInternalEdge_injective n).injOn]

theorem rectangularPrismInternalInteraction_eq_coordinateSums
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismInternalInteraction sigma =
      (∑ x : Fin (2 * n), ∑ y : Fin (2 * n + 1),
        ∑ z : Fin (2 * n + 1),
          rectangularPrismSpin sigma ⟨x.val, by omega⟩ y z *
            rectangularPrismSpin sigma ⟨x.val + 1, by omega⟩ y z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n),
        ∑ z : Fin (2 * n + 1),
          rectangularPrismSpin sigma x ⟨y.val, by omega⟩ z *
            rectangularPrismSpin sigma x ⟨y.val + 1, by omega⟩ z) +
      (∑ x : Fin (2 * n + 1), ∑ y : Fin (2 * n + 1),
        ∑ z : Fin (2 * n),
          rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
            rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩) := by
  unfold rectangularPrismInternalInteraction
  rfl

theorem sum_oddPrismInternalEdges_bond
    (n : Nat)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    (∑ e ∈ oddPrismInternalEdges n, bond sigma e) =
      rectangularPrismInternalInteraction sigma := by
  rw [sum_oddPrismInternalEdges, Fintype.sum_sum_type,
    Fintype.sum_sum_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [oddPrismInternalEdge, bond_mk]
  rw [rectangularPrismInternalInteraction_eq_coordinateSums]
  unfold rectangularPrismSpin
  abel


end
end StatMech.FrontierA
