/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Def.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part4
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem abgrGhostEdgeEquiv_apply (x : V) :
    (abgrGhostEdgeEquiv (V := V) x : Sym2 (Option V)) = s(some x, none) := rfl


theorem abgrCloseGhost_merge_eq
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    abgrCloseGhost (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) =
      abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta := by
  funext e
  by_cases he : e ∈ FieldGhostDict.ghostEdges V
  · rw [show abgrCloseGhost
        (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) e = false by
          simp [abgrCloseGhost, he]]
    exact (abgrMerge_mem (FieldGhostDict.ghostEdges V) (fun _ => false) eta ⟨e, he⟩).symm
  · rw [show abgrCloseGhost
        (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) e =
          abgrMerge (FieldGhostDict.ghostEdges V) gamma eta e by
          simp [abgrCloseGhost, he]]
    rw [abgrMerge_notMem (FieldGhostDict.ghostEdges V) gamma eta ⟨e, he⟩]
    rw [abgrMerge_notMem (FieldGhostDict.ghostEdges V) (fun _ => false) eta ⟨e, he⟩]


end Sharpness
end StatMech
