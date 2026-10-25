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
import Def.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem ndt_starHull_subset_of_fillClosed {K S : Set (Site 2)} (hKS : K ⊆ S)
    (hS : ndt_FillClosed S) : ndt_StarHull K ⊆ S := by
  intro x hx
  induction hx with
  | base h => exact hKS h
  | @fillBL f _ _ ih00 ih11 => exact hS.1 f ih00 ih11
  | @fillTL f _ _ ih10 ih01 => exact hS.2 f ih10 ih01


theorem ndt_fillClosed_product (A B : Set ℤ) : ndt_FillClosed (ndt_product A B) := by
  refine ⟨fun f h00 h11 => ?_, fun f h10 h01 => ?_⟩
  · simp only [ndt_product, Set.mem_setOf_eq, npd_P00, npd_P11, npd_P10,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at *
    exact ⟨h11.1, h00.2⟩
  · simp only [ndt_product, Set.mem_setOf_eq, npd_P10, npd_P01, npd_P00,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at *
    exact ⟨h01.1, h10.2⟩


theorem ndt_starHull_product (A B : Set ℤ) :
    ndt_StarHull (ndt_product A B) = ndt_product A B :=
  Set.Subset.antisymm
    (ndt_starHull_subset_of_fillClosed (le_refl _) (ndt_fillClosed_product A B))
    (ndt_subset_starHull _)


theorem ndt_starHull_box (n : ℕ) : ndt_StarHull (box 2 n) = box 2 n := by
  rw [ndt_box_eq_product, ndt_starHull_product]


theorem ndt_faceMultiplicityOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    usc_FaceMultiplicityOne (ndt_StarHull K) a :=
  emb_faceMultiplicityOne_of_kingSaturated (ndt_StarHull K) a (ndt_kingSaturated_starHull K)


theorem ndt_orbitFaceNoPinch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    OrbitFaceNoPinch (ndt_StarHull K) a :=
  npm_orbitFaceNoPinch (ndt_StarHull K) a (ndt_kingSaturated_starHull K)


theorem ndt_orbit_isCycle (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
    ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl
      (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle :=
  emb_orbit_isCycle_of_kingSaturated (ndt_StarHull K) a hp (ndt_kingSaturated_starHull K)


theorem ndt_box_noDiagTouch (n : ℕ) : npd_NoDiagTouch (box 2 n) :=
  npm_noDiagTouch_of_kingSaturated (ndt_kingSaturated_box n)


theorem ndt_box_faceMultiplicityOne (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e}) :
    usc_FaceMultiplicityOne (box 2 n) a :=
  emb_faceMultiplicityOne_of_kingSaturated (box 2 n) a (ndt_kingSaturated_box n)


theorem ndt_box_orbit_isCycle (n : ℕ)
    (a : {e : Dart // IsBoundaryDart (box 2 n) e})
    (hp : 3 ≤ dartOrbitPeriod (box 2 n) a) :
    ((dartOrbitFaceWalk (box 2 n) a.1 a.2 (dartOrbitPeriod (box 2 n) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 n) a])).IsCycle :=
  emb_orbit_isCycle_of_kingSaturated (box 2 n) a hp (ndt_kingSaturated_box n)


end Lattice
end StatMech
