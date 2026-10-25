/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FloodFillConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Def.StatisticalMechanics.Code.Lattice.FloodFillConnected
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem ffc_offSupportLattice_adj (B : Set (Site 2)) (x y : Site 2) :
    (ffc_offSupportLattice B).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ x ∉ B ∧ y ∉ B := Iff.rfl


theorem ffc_offSupportLattice_le (B : Set (Site 2)) :
    ffc_offSupportLattice B ≤ hypercubicLattice 2 := fun _ _ h => h.1


theorem ffc_offSupportWalk_support {B : Set (Site 2)} {x y : Site 2}
    (w : (ffc_offSupportLattice B).Walk x y) (hx : x ∉ B) :
    ∀ z ∈ w.support, z ∉ B := by
  induction w with
  | nil => intro z hz; rw [SimpleGraph.Walk.support_nil] at hz; rw [List.mem_singleton] at hz;
           exact hz ▸ hx
  | @cons a b c hab p ih =>
    intro z hz
    have hb : b ∉ B := hab.2.2
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with h | h
    · exact h ▸ hx
    · exact ih hb z h


theorem ffc_project_walk {B : Set (Site 2)} {x y : Site 2}
    (w : (ffc_offSupportLattice B).Walk x y) (hx : x ∉ B) :
    ∃ p : (hypercubicLattice 2).Walk x y, (∀ z ∈ p.support, z ∉ B) ∧ p.support = w.support := by
  classical
  refine ⟨w.mapLe (ffc_offSupportLattice_le B), ?_, ?_⟩
  · intro z hz
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
    exact ffc_offSupportWalk_support w hx z hz
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]


end Lattice
end StatMech
