/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Def.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part3
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem abgr_connEvent_iff_exists_active (o : V)
    (omega : ConfigSpace (Sym2 (Option V))) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ x ∈ abgrActive (G := G) o omega, omega s(some x, none) = true := by
  rw [abgr_connEvent_iff_exists_physical G o omega]
  simp only [abgrActive, Finset.mem_filter, Finset.mem_univ, true_and]
  aesop


end Sharpness
end StatMech
