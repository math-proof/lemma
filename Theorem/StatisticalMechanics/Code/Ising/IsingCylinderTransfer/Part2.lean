/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.Ising.IsingCylinderTransfer.Part2
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


theorem isingCylinderBoundaryVector_pos
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h : W -> Real)
    (boundary : ConfigSpace W -> Real) (s : ConfigSpace W) :
    0 < isingCylinderBoundaryVector E J h boundary s := Real.exp_pos _


end
end StatMech.Ising
