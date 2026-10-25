/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part4
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abgrGhostEdgeEquiv :
    V ≃ {e : Sym2 (Option V) // e ∈ FieldGhostDict.ghostEdges V} :=
  Equiv.ofBijective
    (fun x : V => (⟨s(some x, none), by
      simp [FieldGhostDict.ghostEdges]⟩ :
        {e : Sym2 (Option V) // e ∈ FieldGhostDict.ghostEdges V}))
    ⟨by
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      rw [Sym2.eq_iff] at hxy
      rcases hxy with hxy | hxy
      · exact Option.some.inj hxy.1
      · simp at hxy,
    by
      intro e
      rcases e with ⟨e, he⟩
      simp only [FieldGhostDict.ghostEdges, Finset.mem_image,
        Finset.mem_univ, true_and] at he
      obtain ⟨x, rfl⟩ := he
      exact ⟨x, rfl⟩⟩

end Sharpness
end StatMech
