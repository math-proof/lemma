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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part4
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem ginibreChainEdge_oddPrismVerticalChain
    (n : Nat) (x y : Fin (2 * n + 1)) (j : Fin (2 * n)) :
    ginibreChainEdge (oddPrismVerticalChain n x y) j =
      oddPrismInternalEdge n (.inr (.inr (x, y, j))) := by
  simp [ginibreChainEdge, oddPrismVerticalChain, oddPrismInternalEdge,
    Nat.min_eq_left (Nat.le_of_lt j.isLt),
    Nat.min_eq_left (Nat.succ_le_iff.mpr j.isLt)]

theorem ginibreChainEdge_oddPrismVerticalChain_injective
    (n : Nat) (x y : Fin (2 * n + 1)) :
    Function.Injective
      (ginibreChainEdge (N := 2 * n) (oddPrismVerticalChain n x y)) := by
  intro j k hjk
  rw [ginibreChainEdge_oddPrismVerticalChain,
    ginibreChainEdge_oddPrismVerticalChain] at hjk
  have hq := oddPrismInternalEdge_injective n hjk
  have h1 :
      (Sum.inr (x, y, j) :
        (Fin (2 * n + 1) × Fin (2 * n) × Fin (2 * n + 1)) ⊕
          (Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (2 * n))) =
        Sum.inr (x, y, k) := Sum.inr.inj hq
  have h2 : (x, y, j) = (x, y, k) := Sum.inr.inj h1
  exact congrArg (fun q => q.2.2) h2

theorem ginibreChainEdge_oddPrismVerticalChain_mem
    (n : Nat) (x y : Fin (2 * n + 1)) (j : Fin (2 * n)) :
    ginibreChainEdge (oddPrismVerticalChain n x y) j ∈
      oddPrismInternalEdges n := by
  rw [ginibreChainEdge_oddPrismVerticalChain]
  unfold oddPrismInternalEdges
  exact Finset.mem_image.mpr ⟨.inr (.inr (x, y, j)), Finset.mem_univ _, rfl⟩


end
end StatMech.FrontierA
