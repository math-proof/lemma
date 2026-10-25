/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnimalLLN.Part2


namespace StatMech

namespace BeffaraDC

open Finset Filter Topology

open scoped Topology

variable {V : Type*} [DecidableEq V] [Fintype V]


noncomputable def subGreedyAnimalValue (𝒜 : ℕ → Finset (Finset V)) (w : V → ℝ) (n : ℕ) :
    ℝ :=
  if h : (𝒜 n).Nonempty then (𝒜 n).sup' h (fun S => ∑ v ∈ S, w v) else 0


end BeffaraDC
end StatMech
