/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/OuterContourWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsOuterClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.RotationSystemFaces.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Def.StatisticalMechanics.Code.Ising.OuterContourWindingClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


theorem latticeOn_reachable_mem {S : Set (Site 2)} {x y : Site 2} (hx : x ∈ S)
    (hxy : (latticeOn S).Reachable x y) : y ∈ S := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact hx
  | @cons a b c hab p ih => exact ih hab.2.2


theorem mem_outerExteriorComponent_of_exterior {S : Set (Site 2)} {n : ℕ}
    (hS : S ⊆ box 2 n) {x : Site 2} (hx : x ∈ exterior 2 n) :
    x ∈ outerExteriorComponent S n := by
  have hsub : exterior 2 n ⊆ Sᶜ := exterior_subset_compl S n hS
  have hb : beacon 2 n ∈ exterior 2 n := beacon_mem_exterior n (by norm_num)
  have hreach := box_exterior_connected n (by norm_num : 2 ≤ 2)
    (beacon 2 n) x hb hx
  let emb : ((hypercubicLattice 2).induce (exterior 2 n)) →g latticeOn Sᶜ :=
    { toFun := fun z => (z : Site 2)
      map_rel' := fun {a b} hab => ⟨hab, hsub a.2, hsub b.2⟩ }
  exact hreach.map emb


theorem subset_spinCompatibleFill {S : Set (Site 2)} {n : ℕ} (hS : S ⊆ box 2 n) :
    S ⊆ spinCompatibleFill S n := by
  intro x hxS hxext
  have hbext : beacon 2 n ∈ exterior 2 n := beacon_mem_exterior n (by norm_num)
  have hbnot : beacon 2 n ∉ S := (exterior_subset_compl S n hS hbext)
  have hxnot : x ∈ Sᶜ := latticeOn_reachable_mem hbnot hxext
  exact hxnot hxS


theorem spinCompatibleFill_subset_box {S : Set (Site 2)} {n : ℕ} (hS : S ⊆ box 2 n) :
    spinCompatibleFill S n ⊆ box 2 n := by
  intro x hx
  by_contra hxb
  have hxExterior : x ∈ exterior 2 n := by
    rw [exterior_eq_compl_box]
    exact hxb
  exact hx (mem_outerExteriorComponent_of_exterior hS hxExterior)


theorem mem_outerExteriorComponent_adj_iff {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hxS : x ∉ S) (hyS : y ∉ S) :
    x ∈ outerExteriorComponent S n ↔ y ∈ outerExteriorComponent S n := by
  constructor
  · intro hx
    exact hx.trans (show (latticeOn Sᶜ).Adj x y from ⟨hadj, hxS, hyS⟩).reachable
  · intro hy
    exact hy.trans (show (latticeOn Sᶜ).Adj y x from ⟨hadj.symm, hyS, hxS⟩).reachable


theorem outerExteriorComponent_reachable {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hx : x ∈ outerExteriorComponent S n) (hy : y ∈ outerExteriorComponent S n) :
    (latticeOn (outerExteriorComponent S n)).Reachable x y := by
  have transfer : ∀ {a z : Site 2}, (latticeOn Sᶜ).Walk a z →
      a ∈ outerExteriorComponent S n →
      (latticeOn (outerExteriorComponent S n)).Reachable a z := by
    intro a z p ha
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
        have hb : b ∈ outerExteriorComponent S n := ha.trans hab.reachable
        exact (show (latticeOn (outerExteriorComponent S n)).Adj a b from
          ⟨hab.1, ha, hb⟩).reachable.trans (ih hb)
  exact (transfer (Classical.choice hx) (SimpleGraph.Reachable.refl _)).symm.trans
    (transfer (Classical.choice hy) (SimpleGraph.Reachable.refl _))


theorem spinCompatibleFill_compl_reachable {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hx : x ∈ (spinCompatibleFill S n)ᶜ) (hy : y ∈ (spinCompatibleFill S n)ᶜ) :
    (latticeOn (spinCompatibleFill S n)ᶜ).Reachable x y := by
  have hcomp : (spinCompatibleFill S n)ᶜ = outerExteriorComponent S n := by
    simp [spinCompatibleFill]
  rw [hcomp] at hx hy ⊢
  exact outerExteriorComponent_reachable hx hy


theorem spinCompatibleFill_reaches_set {S : Set (Site 2)} {n : ℕ}
    (hS : S ⊆ box 2 n) {x : Site 2} (hx : x ∈ spinCompatibleFill S n) :
    ∃ z ∈ S, (latticeOn (spinCompatibleFill S n)).Reachable x z := by
  obtain ⟨p⟩ := StatMech.Lattice.rsf_reach_all x (beacon 2 n)
  have aux : ∀ {a q : Site 2} (w : (hypercubicLattice 2).Walk a q),
      q ∈ outerExteriorComponent S n → a ∈ spinCompatibleFill S n →
      ∃ z ∈ S, (latticeOn (spinCompatibleFill S n)).Reachable a z := by
    intro a q w hq ha
    induction w with
    | nil => exact False.elim (ha hq)
    | @cons a b c hab w ih =>
        by_cases haS : a ∈ S
        · exact ⟨a, haS, SimpleGraph.Reachable.refl a⟩
        · by_cases hbS : b ∈ S
          · have hbFill : b ∈ spinCompatibleFill S n := subset_spinCompatibleFill hS hbS
            exact ⟨b, hbS,
              (show (latticeOn (spinCompatibleFill S n)).Adj a b from
                ⟨hab, ha, hbFill⟩).reachable⟩
          · have hsame := mem_outerExteriorComponent_adj_iff (n := n) hab haS hbS
            have hbFill : b ∈ spinCompatibleFill S n := by
              intro hbOuter
              exact ha (hsame.mpr hbOuter)
            obtain ⟨z, hzS, hbz⟩ := ih hq hbFill
            exact ⟨z, hzS,
              (show (latticeOn (spinCompatibleFill S n)).Adj a b from
                ⟨hab, ha, hbFill⟩).reachable.trans hbz⟩
  exact aux p (SimpleGraph.Reachable.refl (beacon 2 n)) hx


theorem spinCompatibleFill_connected_from {S : Set (Site 2)} {n : ℕ} {o : Site 2}
    (hS : S ⊆ box 2 n)
    (hconn : ∀ z ∈ S, (latticeOn S).Reachable o z) :
    ∀ x ∈ spinCompatibleFill S n,
      (latticeOn (spinCompatibleFill S n)).Reachable o x := by
  intro x hx
  obtain ⟨z, hzS, hxz⟩ := spinCompatibleFill_reaches_set hS hx
  have hle : latticeOn S ≤ latticeOn (spinCompatibleFill S n) := by
    intro a b hab
    exact ⟨hab.1, subset_spinCompatibleFill hS hab.2.1,
      subset_spinCompatibleFill hS hab.2.2⟩
  exact ((hconn z hzS).mono hle).trans hxz.symm


theorem crosses_of_spinCompatibleFill {S : Set (Site 2)} {n : ℕ} {x y : Site 2}
    (hS : S ⊆ box 2 n) (hadj : (hypercubicLattice 2).Adj x y)
    (hcross : crosses (spinCompatibleFill S n) s(x, y)) : crosses S s(x, y) := by
  rw [crosses_mk] at hcross ⊢
  have hsub := subset_spinCompatibleFill hS
  constructor
  · intro hxS hyS
    exact (hcross.mp (hsub hxS)) (hsub hyS)
  · intro hyS
    by_contra hxS
    have hsame := mem_outerExteriorComponent_adj_iff (n := n) hadj hxS hyS
    have hsameFill : x ∈ spinCompatibleFill S n ↔ y ∈ spinCompatibleFill S n := by
      simpa only [spinCompatibleFill, Set.mem_compl_iff, not_iff_not] using hsame
    have hopposite : x ∈ spinCompatibleFill S n ↔ y ∉ spinCompatibleFill S n := hcross
    tauto


theorem spinCompatibleFill_contourEvent {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    ContourEvent
      (spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n)
      (bondFinsetTouch 2 n) (glue (plusField 2) τ) := by
  intro e he
  unfold crossEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨heB, hcross⟩ := he
  induction e with
  | h x y =>
    rw [crosses_mk] at hcross
    have hadj : (hypercubicLattice 2).Adj x y := adj_of_mem_bondFinsetTouch heB
    have hcluster : crosses (minusCluster (glue (plusField 2) τ) (origin 2)) s(x, y) :=
      crosses_of_spinCompatibleFill (minusCluster_glue_plus_subset_box τ ho) hadj hcross
    rw [bond_mk]
    exact minusCluster_cross_disagree (mem_minusSet.mpr ho) hadj
      ((crosses_mk _ _ _).mp hcluster)


theorem spinCompatibleFill_finite {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n).Finite :=
  (box_finite 2 n).subset
    (spinCompatibleFill_subset_box (minusCluster_glue_plus_subset_box τ ho))


end Ising
end StatMech
