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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part6
open scoped BigOperators
open Finset
open MeasureTheory


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness StatMech.Lattice

noncomputable section

theorem ginibreChainEdge_oddPrismReverseVerticalChain
    (n : Nat) (x y : Fin (2 * n + 1)) (j : Fin (2 * n)) :
    ginibreChainEdge (oddPrismReverseVerticalChain n x y) j =
      oddPrismInternalEdge n
        (.inr (.inr (x, y, oddPrismReverseVerticalEdgeIndex n j))) := by
  unfold ginibreChainEdge oddPrismReverseVerticalChain
    oddPrismInternalEdge oddPrismReverseVerticalEdgeIndex
  rw [Sym2.eq_swap]
  congr 1 <;> simp [RectangularPrismSite.mk.injEq] <;> omega

theorem ginibreChainEdge_oddPrismReverseVerticalChain_injective
    (n : Nat) (x y : Fin (2 * n + 1)) :
    Function.Injective
      (ginibreChainEdge (N := 2 * n)
        (oddPrismReverseVerticalChain n x y)) := by
  intro j k hjk
  rw [ginibreChainEdge_oddPrismReverseVerticalChain,
    ginibreChainEdge_oddPrismReverseVerticalChain] at hjk
  have hq := oddPrismInternalEdge_injective n hjk
  have h1 :
      (Sum.inr (x, y, oddPrismReverseVerticalEdgeIndex n j) :
        (Fin (2 * n + 1) × Fin (2 * n) × Fin (2 * n + 1)) ⊕
          (Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (2 * n))) =
        Sum.inr (x, y, oddPrismReverseVerticalEdgeIndex n k) := Sum.inr.inj hq
  have h2 : (x, y, oddPrismReverseVerticalEdgeIndex n j) =
      (x, y, oddPrismReverseVerticalEdgeIndex n k) := Sum.inr.inj h1
  have hz := congrArg (fun q => q.2.2.val) h2
  apply Fin.ext
  dsimp [oddPrismReverseVerticalEdgeIndex] at hz
  omega

theorem ginibreChainEdge_oddPrismReverseVerticalChain_mem
    (n : Nat) (x y : Fin (2 * n + 1)) (j : Fin (2 * n)) :
    ginibreChainEdge (oddPrismReverseVerticalChain n x y) j ∈
      oddPrismInternalEdges n := by
  rw [ginibreChainEdge_oddPrismReverseVerticalChain]
  unfold oddPrismInternalEdges
  exact Finset.mem_image.mpr
    ⟨.inr (.inr (x, y, oddPrismReverseVerticalEdgeIndex n j)),
      Finset.mem_univ _, rfl⟩

end
end StatMech.FrontierA
