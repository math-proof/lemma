/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech

namespace BeffaraDC

open Finset Filter Topology

open scoped Topology

variable {V : Type*} [DecidableEq V] [Fintype V]


noncomputable def animalsLE (o : V) (n : ℕ) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun S => o ∈ S ∧ S.card ≤ n)


end BeffaraDC
end StatMech
