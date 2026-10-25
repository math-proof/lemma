/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Def.StatisticalMechanics.Code.Ising.PeierlsUncond.Part9
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma origin_mem_minusCluster {σ : ConfigSpace (Site d)} (o : Site d) :
    o ∈ minusCluster σ o := SimpleGraph.Reachable.refl o


lemma minusCluster_subset_minusSet {σ : ConfigSpace (Site d)} {o : Site d}
    (ho : o ∈ minusSet σ) : minusCluster σ o ⊆ minusSet σ := by
  intro x hx
  obtain ⟨w⟩ := (hx : (minusGraph σ).Reachable o x)
  induction w with
  | nil => exact ho
  | @cons a b c hab _ ih => exact ih hab.2.2


lemma minusCluster_cross_disagree {σ : ConfigSpace (Site d)} {o : Site d}
    (ho : o ∈ minusSet σ) {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y)
    (hxy : x ∈ minusCluster σ o ↔ y ∉ minusCluster σ o) :
    spin σ x * spin σ y = -1 := by
  by_cases hx : x ∈ minusCluster σ o
  · have hy : y ∉ minusCluster σ o := hxy.mp hx
    have hxminus : σ x = false := minusCluster_subset_minusSet ho hx
    have hyplus : σ y = true := by
      by_contra hyt
      have hyminus : y ∈ minusSet σ := by
        rw [mem_minusSet, Bool.not_eq_true] at *; exact hyt
      have hadjm : (minusGraph σ).Adj x y :=
        ⟨hadj, minusCluster_subset_minusSet ho hx, hyminus⟩
      exact hy (hx.trans hadjm.reachable)
    unfold spin; rw [hxminus, hyplus]; simp
  · have hy : y ∈ minusCluster σ o := by by_contra hy'; exact hx (hxy.mpr hy')
    have hyminus : σ y = false := minusCluster_subset_minusSet ho hy
    have hxplus : σ x = true := by
      by_contra hxt
      have hxminus : x ∈ minusSet σ := by
        rw [mem_minusSet, Bool.not_eq_true] at *; exact hxt
      have hadjm : (minusGraph σ).Adj y x :=
        ⟨hadj.symm, minusCluster_subset_minusSet ho hy, hxminus⟩
      exact hx (hy.trans hadjm.reachable)
    unfold spin; rw [hxplus, hyminus]; simp


lemma adj_of_mem_bondFinsetTouch {n : ℕ} {x y : Site d}
    (h : s(x, y) ∈ bondFinsetTouch d n) : (hypercubicLattice d).Adj x y := by
  classical
  unfold bondFinsetTouch at h
  rw [Finset.mem_image] at h
  obtain ⟨p, hp, hpe⟩ := h
  unfold bondPairsTouch at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨_, hadj, _⟩ := hp
  rw [Sym2.eq_iff] at hpe
  rcases hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · exact hadj.symm


theorem contourEvent_of_origin_minus {σ : ConfigSpace (Site d)} (n : ℕ)
    (ho : σ (origin d) = false) :
    ContourEvent (minusCluster σ (origin d)) (bondFinsetTouch d n) σ := by
  intro e he
  unfold crossEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨heB, hcr⟩ := he
  induction e with
  | h x y =>
    rw [crosses_mk] at hcr
    have hadj : (hypercubicLattice d).Adj x y := adj_of_mem_bondFinsetTouch (n := n) heB
    rw [bond_mk]
    exact minusCluster_cross_disagree (mem_minusSet.mpr ho) hadj hcr


lemma minusSet_glue_plus_subset_box {n : ℕ} (τ : {x // x ∈ box d n} → Bool) :
    minusSet (glue (plusField d) τ) ⊆ box d n := by
  intro x hx
  by_contra hxbox
  rw [mem_minusSet, glue_not_mem _ _ hxbox] at hx
  simp [plusField] at hx


lemma minusCluster_glue_plus_subset_box {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    minusCluster (glue (plusField d) τ) (origin d) ⊆ box d n := fun _ hx =>
  minusSet_glue_plus_subset_box τ
    (minusCluster_subset_minusSet (mem_minusSet.mpr ho) hx)


lemma minusCluster_glue_plus_finite {n : ℕ} (τ : {x // x ∈ box d n} → Bool)
    (ho : glue (plusField d) τ (origin d) = false) :
    (minusCluster (glue (plusField d) τ) (origin d)).Finite :=
  (box_finite d n).subset (minusCluster_glue_plus_subset_box τ ho)


end Ising
end StatMech
