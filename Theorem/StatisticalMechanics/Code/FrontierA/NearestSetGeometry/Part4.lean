/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NearestSetGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part4
open Set


namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


theorem realizedL1Distances_translate (a : Site d) (A B : Set (Site d)) :
    realizedL1Distances (translateSiteSet a A) (translateSiteSet a B) =
      realizedL1Distances A B := by
  ext n
  simp only [realizedL1Distances, Set.mem_setOf_eq, translateSiteSet,
    Set.mem_image]
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, y', ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨x, hx, y, hy, (l1dist_translate a x y).symm.trans hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨a + x, ⟨x, hx, rfl⟩, a + y, ⟨y, hy, rfl⟩,
      (l1dist_translate a x y).trans hxy⟩


theorem setL1Distance_translate (a : Site d) (A B : Set (Site d)) :
    setL1Distance (translateSiteSet a A) (translateSiteSet a B) =
      setL1Distance A B := by
  unfold setL1Distance
  rw [realizedL1Distances_translate]


theorem nearestSourceSet_translate (a : Site d) (A B : Set (Site d)) :
    nearestSourceSet (translateSiteSet a A) (translateSiteSet a B) =
      translateSiteSet a (nearestSourceSet A B) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, hxz⟩, y', ⟨y, hy, rfl⟩, hdist⟩
    subst z
    refine ⟨x, ⟨hx, y, hy, ?_⟩, rfl⟩
    rw [l1dist_translate, setL1Distance_translate] at hdist
    exact hdist
  · rintro ⟨x, ⟨hx, y, hy, hdist⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, a + y, ⟨y, hy, rfl⟩, ?_⟩
    rw [l1dist_translate, setL1Distance_translate]
    exact hdist


theorem nearestSourceFinset_translate (a : Site d) (A B : Set (Site d)) :
    nearestSourceFinset (translateSiteSet a A) (translateSiteSet a B) =
      (nearestSourceFinset A B).image (fun x => a + x) := by
  classical
  have hinj : Function.Injective (fun x : Site d => a + x) := fun _ _ h =>
    add_left_cancel h
  unfold nearestSourceFinset
  rw [nearestSourceSet_translate]
  by_cases hfin : (nearestSourceSet A B).Finite
  · have himg : (translateSiteSet a (nearestSourceSet A B)).Finite := hfin.image _
    rw [dif_pos himg, dif_pos hfin]
    exact Set.Finite.toFinset_image (fun x => a + x) hfin himg
  · have himg : ¬ (translateSiteSet a (nearestSourceSet A B)).Finite := by
      intro hf
      have hpre : nearestSourceSet A B =
          (fun z : Site d => -a + z) ''
            translateSiteSet a (nearestSourceSet A B) := by
        ext x
        constructor
        · intro hx
          exact ⟨a + x, ⟨x, hx, rfl⟩, by simp⟩
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          simpa using hy
      apply hfin
      rw [hpre]
      exact hf.image _
    simp [himg, hfin]

end StatMech.FrontierA
