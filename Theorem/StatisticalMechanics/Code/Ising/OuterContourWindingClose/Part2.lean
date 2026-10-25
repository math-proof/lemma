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
import Def.StatisticalMechanics.Code.Ising.OuterContourWindingClose.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable


@[simp] theorem coe_spinCompatibleFillFinset {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) =
      spinCompatibleFill (minusCluster (glue (plusField 2) τ) (origin 2)) n :=
  Set.Finite.coe_toFinset _


theorem spinCompatibleFillFinset_isConnected {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    IsConnectedCluster (spinCompatibleFillFinset τ ho) := by
  let M := minusCluster (glue (plusField 2) τ) (origin 2)
  have hMbox : M ⊆ box 2 n := minusCluster_glue_plus_subset_box τ ho
  have hoM : origin 2 ∈ M := origin_mem_minusCluster (origin 2)
  have hMconn : ∀ z ∈ M, (latticeOn M).Reachable (origin 2) z := by
    intro z hz
    exact pcc_walk_transfer (Classical.choice hz) (origin_mem_minusCluster (origin 2))
  have hfill := spinCompatibleFill_connected_from hMbox hMconn
  rw [IsConnectedCluster, coe_spinCompatibleFillFinset]
  refine ⟨?_, ?_⟩
  · rw [spinCompatibleFillFinset, Set.Finite.mem_toFinset]
    exact subset_spinCompatibleFill hMbox hoM
  · intro x hx
    have hx' : x ∈ (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) := hx
    rw [coe_spinCompatibleFillFinset] at hx'
    exact hfill x (by simpa [M] using hx')


theorem spinCompatibleFillFinset_core {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster (spinCompatibleFillFinset τ ho) ∧
      ContourEvent (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
        (bondFinsetTouch 2 n) (glue (plusField 2) τ) := by
  rw [coe_spinCompatibleFillFinset]
  exact ⟨spinCompatibleFill_subset_box (minusCluster_glue_plus_subset_box τ ho),
    spinCompatibleFillFinset_isConnected τ ho, spinCompatibleFill_contourEvent τ ho⟩


theorem latticeOn_le_latticeMinusBarrier (S : Set (Site 2)) :
    latticeOn S ≤ latticeMinusBarrier S := by
  intro a b hab
  rw [latticeMinusBarrier_adj, bdEdge_mk]
  exact ⟨hab.1, by simp [hab.2.1, hab.2.2]⟩


theorem latticeOn_compl_le_latticeMinusBarrier (S : Set (Site 2)) :
    latticeOn Sᶜ ≤ latticeMinusBarrier S := by
  intro a b hab
  rw [latticeMinusBarrier_adj, bdEdge_mk]
  refine ⟨hab.1, ?_⟩
  have ha : a ∉ S := hab.2.1
  have hb : b ∉ S := hab.2.2
  tauto


theorem spinCompatibleFillFinset_faceBoundaryConnected {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    FaceBoundaryConnected
      (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
      (phb_boundarySupport (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
        (spinCompatibleFillFinset τ ho).finite_toSet) := by
  let M := minusCluster (glue (plusField 2) τ) (origin 2)
  let F := spinCompatibleFill M n
  have hMbox : M ⊆ box 2 n := minusCluster_glue_plus_subset_box τ ho
  have hoM : origin 2 ∈ M := origin_mem_minusCluster (origin 2)
  have hoF : origin 2 ∈ F := subset_spinCompatibleFill hMbox hoM
  have hroot : ∀ z ∈ F, (latticeOn F).Reachable (origin 2) z := by
    apply spinCompatibleFill_connected_from hMbox
    intro z hz
    exact pcc_walk_transfer (Classical.choice hz) (origin_mem_minusCluster (origin 2))
  have hin : ∀ a b : Site 2, a ∈ F → b ∈ F →
      (latticeMinusBarrier F).Reachable a b := by
    intro a b ha hb
    exact ((hroot a ha).symm.trans (hroot b hb)).mono
      (latticeOn_le_latticeMinusBarrier F)
  have hout : ∀ a b : Site 2, a ∉ F → b ∉ F →
      (latticeMinusBarrier F).Reachable a b := by
    intro a b ha hb
    have hab : (latticeOn Fᶜ).Reachable a b :=
      spinCompatibleFill_compl_reachable (S := M) (n := n) ha hb
    exact hab.mono (latticeOn_compl_le_latticeMinusBarrier F)
  have hbeacon : beacon 2 n ∉ F := by
    simpa [F, spinCompatibleFill, outerExteriorComponent] using
      (SimpleGraph.Reachable.refl (G := latticeOn Mᶜ) (beacon 2 n))
  have hplanar := faceBoundaryConnected_of_connected_complement F
    (spinCompatibleFill_finite τ ho) hoF hbeacon hin hout
  simpa [F, M, coe_spinCompatibleFillFinset] using hplanar


theorem spinCompatibleFillFinset_planarCore {n : ℕ}
    (τ : {x // x ∈ box 2 n} → Bool)
    (ho : glue (plusField 2) τ (origin 2) = false) :
    (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster (spinCompatibleFillFinset τ ho) ∧
      ContourEvent (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))
        (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧
      ∃ T : Finset (Site 2),
        (faceBoundaryGraph (↑(spinCompatibleFillFinset τ ho) : Set (Site 2))).support ⊆
            (T : Set (Site 2)) ∧
        FaceBoundaryConnected (↑(spinCompatibleFillFinset τ ho) : Set (Site 2)) T := by
  obtain ⟨hbox, hconn, hev⟩ := spinCompatibleFillFinset_core τ ho
  let F : Set (Site 2) := ↑(spinCompatibleFillFinset τ ho)
  let hF : F.Finite := (spinCompatibleFillFinset τ ho).finite_toSet
  refine ⟨hbox, hconn, hev, phb_boundarySupport F hF, ?_, ?_⟩
  · intro f hf
    simpa [F, hF] using hf
  · simpa [F, hF] using spinCompatibleFillFinset_faceBoundaryConnected τ ho


theorem axisAnchor_of_faceBoundaryConnected {n : ℕ} {K : Finset (Site 2)}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) (hKconn : IsConnectedCluster K)
    {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T) :
    ∃ j : ℕ, j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 j ∈ T := by
  classical
  let ω := indicatorConfig K
  have hcluster : cluster 2 ω (origin 2) = (↑K : Set (Site 2)) :=
    cluster_indicatorConfig K hKconn
  have hcluster' : cluster 2 ω (StatMech.Percolation.origin 2) =
      (↑K : Set (Site 2)) := by simpa using hcluster
  have hfin : (cluster 2 ω (origin 2)).Finite := cluster_indicatorConfig_finite K hKconn
  let j := exitIndex (ω := ω) hfin
  let f := exitFaceUp (ω := ω) hfin
  have hexit : (faceBoundaryGraph (↑K : Set (Site 2))).Adj f
      (exitFaceDown (ω := ω) hfin) := by
    have h := exitFaces_faceBoundaryGraph_adj (ω := ω) hfin
    rw [hcluster'] at h
    simpa [f] using h
  have hfT : f ∈ T := hsupp hexit.mem_support_left
  obtain ⟨c, htrail, hcov⟩ :=
    faceBoundaryGraph_single_dualCircuit hsupp hconn hfT
  have hleft : (faceBoundaryGraph (↑K : Set (Site 2))).Adj
      (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
    have h := leftExitFaces_faceBoundaryGraph_adj (ω := ω) hfin
    rwa [hcluster'] at h
  have hled : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈
      c.edges := hcov _ (by rwa [SimpleGraph.mem_edgeSet])
  have hw : leftExitFaceUp (ω := ω) hfin ∈ c.support :=
    c.fst_mem_support_of_mem_edges hled
  have hlt : j < c.length := by
    by_cases hj : j = 0
    · have hne : c.edges ≠ [] := by
        intro he
        rw [he] at hled
        simp at hled
      have hpos : 0 < c.edges.length := List.length_pos_iff.mpr hne
      rw [← SimpleGraph.Walk.length_edges]
      omega
    · have hdist : j ≤ l1dist 2 f (leftExitFaceUp (ω := ω) hfin) := by
        unfold l1dist
        rw [Fin.sum_univ_two]
        have hf0 : f 0 = (j : ℤ) := by simp [f, j, exitFaceUp]
        have hw0 := leftExitFaceUp_coord0_nonpos (ω := ω) hfin
        omega
      have hge : 2 * l1dist 2 f (leftExitFaceUp (ω := ω) hfin) ≤ c.length :=
        closedWalk_length_ge_two_l1dist (faceBoundaryGraph_le (↑K : Set (Site 2))) c hw
      omega
  have hlen := circuit_length_eq_contourLen hKbox c htrail hcov
  have hmaplen : (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length = c.length := by
    unfold SimpleGraph.Walk.mapLe
    exact SimpleGraph.Walk.length_map (Hom.ofLE _) c
  rw [hmaplen] at hlen
  have hfeq : f = axisVertex 2 j := by
    funext i
    fin_cases i <;> simp [f, j, exitFaceUp, axisVertex]
  exact ⟨j, by omega, hfeq ▸ hfT⟩


theorem spinCompatibleFill_outerContourFill (n : ℕ) : OuterContourFill n := by
  intro τ ho
  let K := spinCompatibleFillFinset τ ho
  obtain ⟨hbox, hKconn, hev, T, hsupp, hboundary⟩ :=
    spinCompatibleFillFinset_planarCore τ ho
  obtain ⟨j, hj, hax⟩ := axisAnchor_of_faceBoundaryConnected hbox hKconn hsupp hboundary
  exact ⟨K, hbox, hKconn, hev, T, j, hsupp, hboundary, hj, hax⟩


theorem outerContourWinding_of_outerContourFill (n : ℕ) (h : OuterContourFill n) :
    OuterContourWinding n := by
  intro τ ho
  obtain ⟨K, hKbox, hKconn, hev, T, j, hsupp, hconn, hj, hax⟩ := h τ ho
  
  have hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet,
      e ∈ (componentGraph (↑K : Set (Site 2)) (axisVertex 2 j)).edgeSet :=
    StatMech.Lattice.componentCovers_of_faceBoundaryConnected hsupp hconn hax
  exact ⟨K, hKbox, hKconn, hev, T, j, hsupp, hj, hax, hcov⟩


theorem spinCompatibleFill_outerContourWinding (n : ℕ) : OuterContourWinding n :=
  outerContourWinding_of_outerContourFill n (spinCompatibleFill_outerContourFill n)


theorem peierls_long_range_order_of_outerFill
    (hFill : ∀ n : ℕ, OuterContourFill n) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_outerWinding
    (fun n => outerContourWinding_of_outerContourFill n (hFill n))


theorem peierls_long_range_order_spinCompatibleFill :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_outerFill spinCompatibleFill_outerContourFill


theorem singletonOrigin_outerContourFill_data (n : ℕ) :
    (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧
      IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧
      (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
        ⊆ (singletonBoundarySupport : Set (Site 2)) ∧
      FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
        singletonBoundarySupport ∧
      0 < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧
      axisVertex 2 0 ∈ singletonBoundarySupport := by
  refine ⟨?_, singleton_origin_isConnectedCluster, support_singletonOrigin_subset,
    singletonOrigin_faceBoundaryConnected, ?_, axisVertex_zero_mem_singletonBoundarySupport⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_singleton] at hx
    subst hx; exact origin_mem_box n
  · exact pcc_one_le_contourLen (by norm_num) (fun x hx => by
      rw [Finset.mem_coe, Finset.mem_singleton] at hx; subst hx; exact origin_mem_box n)
      (Finset.mem_singleton_self _)


end Ising
end StatMech
