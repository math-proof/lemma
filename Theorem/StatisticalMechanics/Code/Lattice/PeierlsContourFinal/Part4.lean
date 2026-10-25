/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourFinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn crossEdges contourLen connClusterFamily
  bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem axisContourDualCircuit_of_tightData {n ℓ : ℕ}
    (h : TightAxisCircuitData n ℓ) : AxisContourDualCircuit 2 n ℓ := by
  classical
  refine ⟨dualWalkContour, ?_⟩
  intro F hF
  obtain ⟨K, hKbox, hKcross, hKlen, T, j, hsupp, hj, hax, hcov⟩ := h F hF
  
  obtain ⟨c, htrail, hccov⟩ := dualCircuit_of_componentCovers hsupp hax hcov
  refine ⟨j, hj, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2))), ?_, ?_⟩
  · rw [circuit_length_eq_contourLen hKbox c htrail hccov, hKlen]
  · rw [circuit_decode_eq_contour hKbox c hccov, hKcross]


theorem realisedContourWalkEncoding_of_tightData {n ℓ : ℕ}
    (h : TightAxisCircuitData n ℓ) : RealisedContourWalkEncoding 2 n ℓ :=
  realisedContourWalkEncoding_of_axisCircuit (axisContourDualCircuit_of_tightData h)


theorem contourSubsetCountBound_of_tightData {n ℓ : ℕ}
    (h : TightAxisCircuitData n ℓ) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_walkEncoding (realisedContourWalkEncoding_of_tightData h)


theorem peierls_long_range_order_of_tightData
    (h : ∀ (n ℓ : ℕ), TightAxisCircuitData n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 :=
  peierls_long_range_order_of_walkEncoding (by norm_num)
    (fun n ℓ => realisedContourWalkEncoding_of_tightData (h n ℓ))


theorem componentCovers_of_faceBoundaryConnected {K : Set (Site 2)} {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected K T) {f : Site 2} (hf : f ∈ T) :
    ∀ e ∈ (faceBoundaryGraph K).edgeSet, e ∈ (componentGraph K f).edgeSet := by
  intro e he
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    
    have hxT : x ∈ T := Finset.mem_coe.mp (hsupp he.mem_support_left)
    have hyT : y ∈ T := Finset.mem_coe.mp (hsupp he.symm.mem_support_left)
    have hfT : f ∈ T := hf
    
    have hrI : ((faceBoundaryGraph K).induce (T : Set (Site 2))).Reachable ⟨f, hfT⟩ ⟨x, hxT⟩ :=
      (hconn.preconnected ⟨f, hfT⟩ ⟨x, hxT⟩)
    have hrfx : (faceBoundaryGraph K).Reachable f x := by
      obtain ⟨p⟩ := hrI
      exact ⟨(p.map (SimpleGraph.Embedding.induce (T : Set (Site 2))).toHom).copy rfl rfl⟩
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨he, hrfx, hrfx.trans he.reachable⟩


theorem tightAxisCircuitData_instance {n ℓ : ℕ} {F : Finset (Sym2 (Site 2))}
    {K : Finset (Site 2)} (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
    (hKcross : crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F)
    (hKlen : contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ)
    {T : Finset (Site 2)}
    (hsupp : (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)))
    (hconn : FaceBoundaryConnected (↑K : Set (Site 2)) T)
    {j : ℕ} (hj : j < ℓ) (hax : axisVertex 2 j ∈ T) :
    ∃ K' : Finset (Site 2), (↑K' : Set (Site 2)) ⊆ box 2 n ∧
      crossEdges (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧
      contourLen (↑K' : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ ∧
      ∃ (T' : Finset (Site 2)) (j' : ℕ),
        (faceBoundaryGraph (↑K' : Set (Site 2))).support ⊆ (T' : Set (Site 2)) ∧
        j' < ℓ ∧ axisVertex 2 j' ∈ T' ∧
        (∀ e ∈ (faceBoundaryGraph (↑K' : Set (Site 2))).edgeSet,
          e ∈ (componentGraph (↑K' : Set (Site 2)) (axisVertex 2 j')).edgeSet) :=
  ⟨K, hKbox, hKcross, hKlen, T, j, hsupp, hj, hax,
    componentCovers_of_faceBoundaryConnected hsupp hconn hax⟩


theorem axisVertex_two_zero : axisVertex 2 0 = (![0, 0] : Site 2) := by
  funext i; fin_cases i <;> simp [axisVertex]


theorem axisVertex_zero_mem_singletonBoundarySupport :
    axisVertex 2 0 ∈ singletonBoundarySupport := by
  rw [axisVertex_two_zero]; exact mem_singletonBoundarySupport_00


theorem singletonOrigin_tight_dualCircuit :
    ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
        (axisVertex 2 0) (axisVertex 2 0),
      c.IsTrail ∧
        ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
          e ∈ c.edges := by
  have hcov := componentCovers_of_faceBoundaryConnected
    (K := (↑({origin 2} : Finset (Site 2)) : Set (Site 2))) (T := singletonBoundarySupport)
    support_singletonOrigin_subset singletonOrigin_faceBoundaryConnected
    axisVertex_zero_mem_singletonBoundarySupport
  exact dualCircuit_of_componentCovers support_singletonOrigin_subset
    axisVertex_zero_mem_singletonBoundarySupport hcov


theorem singletonOrigin_componentCovers :
    ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
      e ∈ (componentGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
        (axisVertex 2 0)).edgeSet :=
  componentCovers_of_faceBoundaryConnected support_singletonOrigin_subset
    singletonOrigin_faceBoundaryConnected axisVertex_zero_mem_singletonBoundarySupport


theorem axisVertex_two_natCast (m : ℕ) : axisVertex 2 m = (![(m : ℤ), 0] : Site 2) := by
  funext i; fin_cases i <;> simp [axisVertex]


theorem axisVertex_m_mem_boxFrame (m n : ℕ) : axisVertex 2 m ∈ boxFrame m n := by
  rw [axisVertex_two_natCast]
  exact mem_boxFrame_right m n 0 (by omega) (by positivity)


theorem boxCluster_componentCovers (m n : ℕ) :
    ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet,
      e ∈ (componentGraph (↑(boxCluster m n) : Set (Site 2)) (axisVertex 2 m)).edgeSet :=
  componentCovers_of_faceBoundaryConnected (support_boxCluster_subset_frame m n)
    (boxCluster_faceBoundaryConnected m n) (axisVertex_m_mem_boxFrame m n)


theorem boxCluster_tight_dualCircuit (m n : ℕ) :
    ∃ c : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        (axisVertex 2 m) (axisVertex 2 m),
      c.IsTrail ∧
        ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet, e ∈ c.edges :=
  dualCircuit_of_componentCovers (support_boxCluster_subset_frame m n)
    (axisVertex_m_mem_boxFrame m n) (boxCluster_componentCovers m n)


theorem tightAxisCircuitData_of_empty {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : TightAxisCircuitData n ℓ := by
  intro F hF
  rw [hempty] at hF
  simp at hF


theorem contourSubsetCountBound_of_empty_tightData {n ℓ : ℕ}
    (hempty : realisedContours 2 n ℓ = ∅) : ContourSubsetCountBound 2 n ℓ :=
  contourSubsetCountBound_of_tightData (tightAxisCircuitData_of_empty hempty)

end Lattice
end StatMech
