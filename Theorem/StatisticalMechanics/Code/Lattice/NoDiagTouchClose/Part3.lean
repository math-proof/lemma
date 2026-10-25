/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/NoDiagTouchClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Def.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem ndt_subset_starHull (K : Set (Site 2)) : K ⊆ ndt_StarHull K :=
  fun _ h => ndt_StarHullMem.base h


theorem ndt_kingSaturated_starHull (K : Set (Site 2)) : npm_KingSaturated (ndt_StarHull K) := by
  intro f
  exact ⟨fun h00 h11 => Or.inl (ndt_StarHullMem.fillBL h00 h11),
         fun h10 h01 => Or.inl (ndt_StarHullMem.fillTL h10 h01)⟩


theorem ndt_noDiagTouch (K : Set (Site 2)) : npd_NoDiagTouch (ndt_StarHull K) :=
  npm_noDiagTouch_of_kingSaturated (ndt_kingSaturated_starHull K)


theorem ndt_starHull_empty : ndt_StarHull (∅ : Set (Site 2)) = ∅ := by
  ext x
  simp only [ndt_StarHull, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  induction hx with
  | base h => exact h
  | fillBL _ _ ih00 _ => exact ih00
  | fillTL h10 _ ih10 _ => exact ih10


end Lattice
end StatMech
