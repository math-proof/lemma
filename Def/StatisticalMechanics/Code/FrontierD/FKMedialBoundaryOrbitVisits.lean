/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryOrbitVisits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitReachability
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


def permOrbitVisitCount {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) (d e : α) : Nat :=
  ∑ i : Fin (orderOf σ), if (σ ^ (i : Nat)) d = e then 1 else 0

end
end StatMech.FrontierD
