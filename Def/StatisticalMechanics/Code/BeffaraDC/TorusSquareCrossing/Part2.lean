/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusAmbientSwapEdgeEquiv (L : ℕ) [Fact (2 < L)] :
    TorusAmbientEdge L ≃ TorusAmbientEdge L where
  toFun e := ⟨Sym2.map (torusCoordSwap L) e.1,
    (torusCoordSwap_mem_edgeFinset_iff L e.1).2 e.2⟩
  invFun e := ⟨Sym2.map (torusCoordSwap L) e.1,
    (torusCoordSwap_mem_edgeFinset_iff L e.1).2 e.2⟩
  left_inv e := by
    apply Subtype.ext
    change Sym2.map (torusCoordSwap L)
      (Sym2.map (torusCoordSwap L) e.1) = e.1
    induction e.1 using Sym2.ind with
    | _ x y => simp [torusCoordSwap]
  right_inv e := by
    apply Subtype.ext
    change Sym2.map (torusCoordSwap L)
      (Sym2.map (torusCoordSwap L) e.1) = e.1
    induction e.1 using Sym2.ind with
    | _ x y => simp [torusCoordSwap]


noncomputable def torusAmbientSwapConfig (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : TorusAmbientConfig L :=
  fun e => omega ((torusAmbientSwapEdgeEquiv L).symm e)


noncomputable def torusAmbientSwapConfigEquiv (L : ℕ) [Fact (2 < L)] :
    TorusAmbientConfig L ≃ TorusAmbientConfig L where
  toFun := torusAmbientSwapConfig L
  invFun eta := fun e => eta (torusAmbientSwapEdgeEquiv L e)
  left_inv omega := by
    funext e
    simp [torusAmbientSwapConfig]
  right_inv omega := by
    funext e
    simp [torusAmbientSwapConfig]


end StatMech.BeffaraDC
