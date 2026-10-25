/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentConnectivityApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.FrontierB.CurrentConnectivityApproximation
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}


theorem boxConnectionEvent_mono (x y : Site d) :
    Monotone (fun n => boxConnectionEvent n x y) := by
  intro m n hmn omega homega
  obtain ⟨hx, hy, hconn⟩ := homega
  have hsub : box d m ⊆ box d n := box_mono d hmn
  exact ⟨hsub hx, hsub hy,
    connectedWithin_mono_set' omega hsub hconn⟩


theorem mem_iUnion_boxConnectionEvent_iff_connected
    (omega : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    omega ∈ (⋃ n, boxConnectionEvent n x y) ↔ Connected d omega x y := by
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨n, hx, hy, hconn⟩
    exact hconn.connected
  · rintro ⟨w⟩
    obtain ⟨n, hn⟩ := finite_subset_box
      (↑w.support.toFinset : Set (Site d)) (w.support.toFinset.finite_toSet)
    have hw : ∀ z ∈ w.support, z ∈ box d n := fun z hz => hn (by simpa using hz)
    have hx : x ∈ box d n := hw x w.start_mem_support
    have hy : y ∈ box d n := hw y w.end_mem_support
    rw [Set.mem_iUnion]
    refine ⟨n, hx, hy, ?_⟩
    exact ⟨w.induce (box d n) hw⟩


theorem iUnion_boxConnectionEvent (x y : Site d) :
    (⋃ n, boxConnectionEvent n x y) =
      {omega | Connected d omega x y} := by
  ext omega
  exact mem_iUnion_boxConnectionEvent_iff_connected omega x y


theorem isClopen_boxConnectionEvent (n : ℕ) (x y : Site d) :
    IsClopen (boxConnectionEvent n x y) := by
  let S := boxFinset d n
  have hS : (S : Set (Site d)) = box d n := by
    ext z
    simp [S]
  have hdep : DependsOn
      ((boxConnectionEvent n x y).indicator (fun _ => (1 : ℝ)))
        (edgesWithinFinset S : Set (Sym2 (Site d))) := by
    simpa only [boxConnectionEvent, hS] using
      (withinConn_dependsOn S x y)
  rw [eq_cylinder_restrict_image _ _ hdep]
  exact isClopen_cylinderEvent _ _


end StatMech.FrontierB
