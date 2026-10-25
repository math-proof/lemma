/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc50hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc51refute
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc51_hallCondComp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) : Bool :=
  decide (∀ W ∈ (rc20_famCylBoxComp n 𝒜 ℬ).powerset,
    W.card ≤ (W.biUnion (rc51_neighbourhoodComp n 𝒜 ℬ)).card)

end StatMech.Walls
