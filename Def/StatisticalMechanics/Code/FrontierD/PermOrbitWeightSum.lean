/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/PermOrbitWeightSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryOrbitVisits.Part2
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

def permOrbitWeightSum {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (σ : Perm α) (d : α) (f : α → A) : A :=
  ∑ i : Fin (orderOf σ), f ((σ ^ (i : Nat)) d)


def permCycleClassWeightSum {α A : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid A] (σ : Perm α) (d : α) (f : α → A) : A :=
  ∑ x : α, if σ.SameCycle d x then f x else 0

end
end StatMech.FrontierD
