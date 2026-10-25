/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnimalLLN


namespace StatMech

namespace BeffaraDC

open Finset Filter Topology

open scoped Topology

variable {V : Type*} [DecidableEq V] [Fintype V]


noncomputable def greedyAnimalValue (w : V → ℝ) (o : V) (n : ℕ) : ℝ :=
  if h : (animalsLE o n).Nonempty then
    (animalsLE o n).sup' h (fun S => ∑ v ∈ S, w v)
  else 0


end BeffaraDC
end StatMech
