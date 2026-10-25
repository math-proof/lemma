/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.PivotalFactorFull.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open MeasureTheory Set Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem shk_mem_boundaryEdges_iff {S : Finset (Site d)} {x y : Site d} :
    (x, y) ∈ boundaryEdges d S ↔
      x ∈ S ∧ y ∉ S ∧ (hypercubicLattice d).Adj x y := by
  classical
  constructor
  · intro hxy
    rw [boundaryEdges, Finset.mem_image] at hxy
    obtain ⟨t, ht, hteq⟩ := hxy
    rw [Finset.mem_filter] at ht
    obtain ⟨htmem, hyout⟩ := ht
    rw [Finset.mem_product] at htmem
    obtain ⟨hxS, htcoords⟩ := htmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hteq.symm
    refine ⟨hxS, hyout, ?_⟩
    change NearestNeighbour d t.1
      (coordShift t.1 t.2.1 (stepSign t.2.2))
    rw [nearestNeighbour_iff_shift]
    refine ⟨t.2.1, stepSign t.2.2, ?_, rfl⟩
    cases t.2.2 <;> simp [stepSign]
  · rintro ⟨hxS, hyS, hxy⟩
    change NearestNeighbour d x y at hxy
    rw [nearestNeighbour_iff_shift] at hxy
    obtain ⟨i, sgn, hsgn, rfl⟩ := hxy
    rcases hsgn with rfl | rfl
    · rw [boundaryEdges, Finset.mem_image]
      refine ⟨(x, (i, true)), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hxS, ⟨Finset.mem_univ i, Finset.mem_univ true⟩⟩,
          by simpa [coordShift, stepSign, Lattice.shift] using hyS⟩
      · rfl
    · rw [boundaryEdges, Finset.mem_image]
      refine ⟨(x, (i, false)), ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hxS, ⟨Finset.mem_univ i, Finset.mem_univ false⟩⟩,
          by simpa [coordShift, stepSign, Lattice.shift] using hyS⟩
      · rfl


theorem shk_firstExit_inclusion_lattice (A : Set (Site d))
    (S : Finset (Site d)) (B : Set (Site d)) (u : Site d)
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    connEvent (hypercubicLattice d) A u B ⊆
      ⋃ q ∈ boundaryEdges d S,
        disjointOccurrence
          (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1})
          (disjointOccurrence (edgeOpenEvent q.1 q.2)
            (connEvent (hypercubicLattice d) A q.2 B)) := by
  intro omega homega
  simp only [connEvent, Set.mem_setOf_eq] at homega
  obtain ⟨b, hbA, hbB, path, hsupp⟩ :=
    shk_walk_of_connToSet (hypercubicLattice d) omega A u B homega
  have hbypass_supp : ∀ z ∈ path.bypass.support, z ∈ A := fun z hz =>
    hsupp z (path.support_bypass_subset hz)
  have hbS : b ∉ (S : Set (Site d)) := hBS b hbB
  obtain ⟨x, y, hxS, hyS, hadj, htriple⟩ :=
    shk_firstExit_triple (hypercubicLattice d) omega A (S : Set (Site d)) B
      u b huS hbB hbS path.bypass path.bypass_isPath hbypass_supp
  rw [Set.mem_iUnion₂]
  exact ⟨(x, y), shk_mem_boundaryEdges_iff.mpr ⟨hxS, hyS, hadj⟩, htriple⟩


theorem shk_connEvent_singleton_eq_connWithinEvent (T : Set (Site d))
    (u x : Site d) :
    connEvent (hypercubicLattice d) T u {x} = connWithinEvent d T u x := by
  ext omega
  constructor
  · rintro ⟨hu, b, hbT, rfl, hconn⟩
    exact ⟨hu, hbT, hconn⟩
  · rintro ⟨hu, hx, hconn⟩
    exact ⟨hu, x, hx, rfl, hconn⟩


theorem shk_connEvent_singleton_dependsOn (T : Finset (Site d)) (u x : Site d) :
    DependsOn (connEvent (hypercubicLattice d) (T : Set (Site d)) u {x})
      (internalEdgesFinset T : Set (Sym2 (Site d))) := by
  rw [shk_connEvent_singleton_eq_connWithinEvent]
  exact ih_event_dependsOn_of_indicator shp_connWithinEvent_dependsOn


theorem shk_edgeOpenEvent_dependsOn (x y : Site d) :
    DependsOn (edgeOpenEvent x y)
      ({s(x, y)} : Set (Sym2 (Site d))) := by
  exact ih_event_dependsOn_of_indicator (by
    simpa only [edgeOpenEvent] using
      (coord_true_dependsOn (E := Sym2 (Site d)) s(x, y)))


end Sharpness
end StatMech
