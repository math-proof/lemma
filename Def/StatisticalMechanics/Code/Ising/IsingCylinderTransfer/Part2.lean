/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCylinderTransfer
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


def isingCylinderBoundaryVector
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h : W -> Real)
    (boundary : ConfigSpace W -> Real) (s : ConfigSpace W) : Real :=
  Real.exp (cylinderLayerInteraction E J h s / 2 + boundary s)

end
end StatMech.Ising
