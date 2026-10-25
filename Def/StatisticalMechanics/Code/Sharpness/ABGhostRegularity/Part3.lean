/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part3
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abgrActive (o : V) (omega : ConfigSpace (Sym2 (Option V))) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun x =>
      abgrCloseGhost omega ∈ connEvent (withGhost G) Set.univ (some o) {some x}

end Sharpness
end StatMech
