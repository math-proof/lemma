/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TreeNonBridgeProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces.Part3
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
import Def.StatisticalMechanics.Code.Lattice.TreeNonBridgeProve
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {V : Type*}


theorem tnbp_reachable_insert_of_ringConnected {c : Site 2} {B : Set (Site 2)}
    (hring : tnbp_RingConnected c B) {x y : Site 2} (hx : x ≠ c) (hy : y ≠ c)
    (hr : (ffc_offSupportLattice B).Reachable x y) :
    (ffc_offSupportLattice (insert c B)).Reachable x y :=
  tnbp_reachable_of_avoid (ffc_offSupportLattice B) (ffc_offSupportLattice (insert c B)) c
    (tnbp_insert_adj_iff c B) hring hx hy hr


theorem tnbp_step_reachable (B' : Set (Site 2)) {a b : Site 2}
    (hadj : (hypercubicLattice 2).Adj a b) (ha : a ∉ B') (hb : b ∉ B') :
    (ffc_offSupportLattice B').Reachable a b :=
  SimpleGraph.Adj.reachable ⟨hadj, ha, hb⟩


theorem tnbp_neighbour_cases {c p : Site 2} (h : (hypercubicLattice 2).Adj c p) :
    p = ![c 0 + 1, c 1] ∨ p = ![c 0 - 1, c 1] ∨ p = ![c 0, c 1 + 1] ∨ p = ![c 0, c 1 - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  have hp : p = ![p 0, p 1] := by funext i; fin_cases i <;> rfl
  have key : (p 0 = c 0 + 1 ∧ p 1 = c 1) ∨ (p 0 = c 0 - 1 ∧ p 1 = c 1) ∨
             (p 0 = c 0 ∧ p 1 = c 1 + 1) ∨ (p 0 = c 0 ∧ p 1 = c 1 - 1) := by omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl (by rw [hp, h0, h1])
  · exact Or.inr (Or.inl (by rw [hp, h0, h1]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hp, h0, h1])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hp, h0, h1])))


end Lattice
end StatMech
