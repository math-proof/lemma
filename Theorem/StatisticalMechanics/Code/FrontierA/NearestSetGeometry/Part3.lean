/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part3
open Set


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


theorem mem_nearestSourceFinset_iff {A B : Set (Site d)}
    (hfin : (nearestSourceSet A B).Finite) (x : Site d) :
    x ∈ nearestSourceFinset A B ↔ x ∈ nearestSourceSet A B := by
  classical
  simp [nearestSourceFinset, hfin]


theorem mem_nearestSourceSet_of_mem_finset {A B : Set (Site d)} {x : Site d}
    (hx : x ∈ nearestSourceFinset A B) : x ∈ nearestSourceSet A B := by
  classical
  by_cases hfin : (nearestSourceSet A B).Finite
  · exact (mem_nearestSourceFinset_iff hfin x).1 hx
  · simp [nearestSourceFinset, hfin] at hx


theorem mem_nearestSourceFinset_iff_finite {A B : Set (Site d)} {x : Site d} :
    x ∈ nearestSourceFinset A B ↔
      (nearestSourceSet A B).Finite ∧ x ∈ nearestSourceSet A B := by
  classical
  by_cases hfin : (nearestSourceSet A B).Finite
  · simp [nearestSourceFinset, hfin, Set.Finite.mem_toFinset]
  · simp [nearestSourceFinset, hfin]


theorem nearestSourceFinset_card (A B : Set (Site d)) :
    (nearestSourceFinset A B).card = (nearestSourceSet A B).ncard := by
  classical
  by_cases hfin : (nearestSourceSet A B).Finite
  · simp [nearestSourceFinset, hfin, Set.ncard, Set.Finite.toFinset]
  · have hinf : (nearestSourceSet A B).Infinite := by
      by_contra hni
      exact hfin (Set.not_infinite.mp hni)
    simp [nearestSourceFinset, hfin, hinf.ncard]


theorem nearestSourceFinset_nonempty {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hfin : (nearestSourceSet A B).Finite) :
    (nearestSourceFinset A B).Nonempty := by
  obtain ⟨x, hx⟩ := nearestSourceSet_nonempty hA hB
  exact ⟨x, (mem_nearestSourceFinset_iff hfin x).2 hx⟩


theorem l1dist_translate (a x y : Site d) :
    l1dist d (a + x) (a + y) = l1dist d x y := by
  unfold l1dist
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Pi.add_apply]
  ring


end StatMech.FrontierA
