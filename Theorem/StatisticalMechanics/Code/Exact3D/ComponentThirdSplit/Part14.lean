/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part14
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n}
    {x : Option (FK.boxVerts 3 n)} :
    x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v ↔
      x ≠ none ∧
        x ≠ some (IsingFK.boxOrigin 3 n) ∧
        x ≠ some v := by
  classical
  simp [finiteBoundaryGhostSourceClassEndpointUnmarkedOptions]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card =
      Fintype.card (FK.boxVerts 3 n) - 2 := by
  classical
  let o : FK.boxVerts 3 n := IsingFK.boxOrigin 3 n
  have hvbdry : FK.boxBoundary 3 n v := (Finset.mem_filter.mp hv).2
  have hov : o ≠ v := boxOrigin_ne_of_boxBoundary 3 n hvbdry
  have hset :
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v =
        (((Finset.univ : Finset (Option (FK.boxVerts 3 n))).erase none).erase
          (some o)).erase (some v) := by
    ext x
    simp [
      finiteBoundaryGhostSourceClassEndpointUnmarkedOptions, o,
      and_left_comm, and_comm]
  have hnone :
      (none : Option (FK.boxVerts 3 n)) ∈
        (Finset.univ : Finset (Option (FK.boxVerts 3 n))) :=
    Finset.mem_univ _
  have horigin :
      (some o : Option (FK.boxVerts 3 n)) ∈
        (Finset.univ : Finset (Option (FK.boxVerts 3 n))).erase none := by
    simp [o]
  have hvo : v ≠ o := fun h => hov h.symm
  have hvSome :
      (some v : Option (FK.boxVerts 3 n)) ∈
        ((Finset.univ : Finset (Option (FK.boxVerts 3 n))).erase none).erase
          (some o) := by
    simp [o, hvo]
  rw [hset]
  rw [Finset.card_erase_of_mem hvSome]
  rw [Finset.card_erase_of_mem horigin]
  rw [Finset.card_erase_of_mem hnone]
  rw [Finset.card_univ, Fintype.card_option]
  omega

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card =
      (2 * n + 1) ^ 3 - 2 := by
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv,
    StatMech.FK.ecz_boxVerts_card]

end Exact3D
end StatMech
