/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MedialTwoEdgeSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialSwitchCount
open SimpleGraph Set


namespace StatMech.Universality

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def medialTwoEdgeSwitch (G : SimpleGraph V) (a b c d : V) : SimpleGraph V :=
  ((G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b)


end
end StatMech.Universality
