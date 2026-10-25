/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourEncodingClose
open Set Finset SimpleGraph
open StatMech.Ising


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


@[simp] theorem indicatorConfig_mk (K : Finset (Site d)) (x y : Site d) :
    indicatorConfig K s(x, y) = decide (x ∈ K ∧ y ∈ K) := rfl


theorem openSubgraph_indicatorConfig (K : Finset (Site d)) :
    openSubgraph d (indicatorConfig K) = latticeOn (↑K : Set (Site d)) := by
  ext x y
  rw [openSubgraph_adj]
  show ((hypercubicLattice d).Adj x y ∧ indicatorConfig K s(x, y) = true) ↔
    (latticeOn (↑K : Set (Site d))).Adj x y
  rw [show (latticeOn (↑K : Set (Site d))).Adj x y ↔
    (hypercubicLattice d).Adj x y ∧ x ∈ (↑K : Set (Site d)) ∧ y ∈ (↑K : Set (Site d)) from Iff.rfl]
  simp only [indicatorConfig_mk, decide_eq_true_eq, Finset.mem_coe]


theorem cluster_indicatorConfig (K : Finset (Site d)) (hconn : IsConnectedCluster K) :
    cluster d (indicatorConfig K) (origin d) = (↑K : Set (Site d)) := by
  ext x
  rw [mem_cluster]
  constructor
  · intro hx
    rw [Connected, openSubgraph_indicatorConfig] at hx
    obtain ⟨w⟩ := hx
    have key : ∀ {a b : Site d}, (latticeOn (↑K : Set (Site d))).Walk a b → a ∈ K → b ∈ K := by
      intro a b w
      induction w with
      | nil => exact fun h => h
      | @cons a b c hab w ih => intro _; exact ih (by simpa using hab.2.2)
    exact key w hconn.1
  · intro hx
    rw [Connected, openSubgraph_indicatorConfig]
    exact hconn.2 x (by simpa using hx)


theorem cluster_indicatorConfig_finite (K : Finset (Site d)) (hconn : IsConnectedCluster K) :
    (cluster d (indicatorConfig K) (origin d)).Finite := by
  rw [cluster_indicatorConfig K hconn]
  exact K.finite_toSet


end Lattice
end StatMech
