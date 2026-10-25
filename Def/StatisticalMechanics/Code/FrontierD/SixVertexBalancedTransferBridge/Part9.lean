/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part8
open Finset Matrix


namespace StatMech.FrontierD

def svTorusHorizontalRows (T : EvenTorus) (omega : SixVertexArrows T) :
    Fin T.height → SixVertexRow T.width :=
  fun j i => omega.horizontal (i, j)

def svTorusVerticalRows (T : EvenTorus) (omega : SixVertexArrows T) :
    Fin T.height → SixVertexRow T.width :=
  fun j i => omega.vertical (i, j)

def svTorusRowsEquiv (T : EvenTorus) :
    SixVertexArrows T ≃
      (Fin T.height → SixVertexRow T.width) ×
        (Fin T.height → SixVertexRow T.width) where
  toFun omega := (svTorusHorizontalRows T omega, svTorusVerticalRows T omega)
  invFun rows :=
    { horizontal := fun ij => rows.1 ij.2 ij.1
      vertical := fun ij => rows.2 ij.2 ij.1 }
  left_inv omega := by
    apply SixVertexArrows.ext <;> funext ij <;> rfl
  right_inv rows := by
    apply Prod.ext <;> funext j i <;> rfl

end StatMech.FrontierD
