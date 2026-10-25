/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

section FiniteProduct

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def abgrMerge (s : Finset E) (gamma : {e // e ∈ s} -> Bool)
    (eta : {e // e ∉ s} -> Bool) : ConfigSpace E :=
  (Equiv.piEquivPiSubtypeProd (fun e : E => e ∈ s) (fun _ => Bool)).symm (gamma, eta)

end FiniteProduct
end Sharpness
end StatMech
