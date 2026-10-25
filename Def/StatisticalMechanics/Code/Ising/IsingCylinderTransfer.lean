/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PositiveTransferObservable
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open Finset Matrix Filter Topology
open scoped BigOperators


namespace StatMech.Ising

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]


def cylinderLayerInteraction
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h : W -> Real)
    (s : ConfigSpace W) : Real :=
  (∑ e ∈ E, J e * bond s e) + ∑ x : W, h x * spin s x


def cylinderInterLayerInteraction
    (Jvertical : W -> Real) (s t : ConfigSpace W) : Real :=
  ∑ x : W, Jvertical x * spin s x * spin t x


def isingCylinderTransfer
    (E : Finset (Sym2 W)) (J : Sym2 W -> Real) (h Jvertical : W -> Real) :
    Matrix (ConfigSpace W) (ConfigSpace W) Real :=
  fun s t => Real.exp
    (cylinderLayerInteraction E J h s / 2 +
      cylinderInterLayerInteraction Jvertical s t +
      cylinderLayerInteraction E J h t / 2)

end
end StatMech.Ising
