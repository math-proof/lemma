/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Def.StatisticalMechanics.Code.Lattice.InterfaceConnected
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dartNext_iterate_head_fixed (K : Set (Site 2)) (e : Dart) :
    ∀ (k : ℕ), (∀ j < k, IsInnerCorner K ((dartNext K)^[j] e)) →
      ((dartNext K)^[k] e).head = e.head ∧
      ((dartNext K)^[k] e).dir = (rot90Fun)^[k] e.dir := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro hcorner
    have hm : ∀ j < m, IsInnerCorner K ((dartNext K)^[j] e) := fun j hj =>
      hcorner j (Nat.lt_succ_of_lt hj)
    obtain ⟨hh, hd⟩ := ih hm
    have hcm : IsInnerCorner K ((dartNext K)^[m] e) := hcorner m (Nat.lt_succ_self m)
    have hstep := dartNext_front_head K ((dartNext K)^[m] e) hcm
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · rw [hstep.1, hh]
    · rw [hstep.2, hd, ← Function.iterate_succ_apply' rot90Fun m e.dir]


theorem dartNext_iterate_isBoundary_head_fixed (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (k : ℕ)
    (hcorner : ∀ j < k, IsInnerCorner K ((dartNext K)^[j] e)) :
    IsBoundaryDart K ((dartNext K)^[k] e) ∧
      ((dartNext K)^[k] e).head = e.head ∧
      ((dartNext K)^[k] e).dir = (rot90Fun)^[k] e.dir := by
  refine ⟨iterate_isBoundaryDart' K e he k, dartNext_iterate_head_fixed K e k hcorner⟩


end Lattice
end StatMech
