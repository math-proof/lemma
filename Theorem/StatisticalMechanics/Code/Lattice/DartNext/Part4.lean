/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Def.StatisticalMechanics.Code.Lattice.DartNext.Part4
open SimpleGraph


namespace StatMech

namespace Lattice

theorem dartNext_of_front_mem (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    dartNext K e = mkDart (e.head + (-rot90Fun e.dir)) (rot90Fun e.dir)
      (unitWt_rot90Fun_dir e) := by
  classical
  unfold dartNext; rw [if_pos h]


theorem dartNext_front_head (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).head = e.head ∧ (dartNext K e).dir = rot90Fun e.dir := by
  classical
  refine ⟨?_, ?_⟩
  · rw [dartNext_of_front_mem K e h, mkDart_head]; abel
  · rw [dartNext_of_front_mem K e h, mkDart_dir]


theorem dartNext_of_side_mem (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    dartNext K e = mkDart (e.tail + (-rot90Fun e.dir)) e.dir (unitWt_dir e) := by
  classical
  unfold dartNext; rw [if_neg h1, if_pos h2]


theorem dartNext_of_corner (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    dartNext K e = mkDart e.tail (-rot90Fun e.dir) (unitWt_neg_rot90Fun_dir e) := by
  classical
  unfold dartNext; rw [if_neg h1, if_neg h2]


theorem dartNext_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) : IsBoundaryDart K (dartNext K e) := by
  classical
  obtain ⟨hc, hv⟩ := he
  unfold dartNext IsBoundaryDart
  split_ifs with h1 h2
  · 
    refine ⟨by simpa using h1, ?_⟩
    rw [mkDart_head]
    have : e.head + -rot90Fun e.dir + rot90Fun e.dir = e.head := by abel
    rw [this]; exact hv
  · 
    refine ⟨by simpa using h2, ?_⟩
    rw [mkDart_head]
    have : e.tail + -rot90Fun e.dir + e.dir = e.head + -rot90Fun e.dir := by
      rw [Dart.dir_def]; abel
    rw [this]; exact h1
  · 
    exact ⟨by simpa using hc, by simpa using h2⟩

end Lattice
end StatMech
