/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect
    {a b c d : Int} {f g : Site 2}
    (hf : f ∈ rect a (b - 1) c (d - 1))
    (hfg : (hypercubicLattice 2).Adj f g) :
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ rect a b c d ∧ q ∈ rect a b c d := by
  rw [mem_rect] at hf
  rcases face_adj_dir hfg with rfl | rfl | rfl | rfl
  · refine ⟨![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega

    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![f 0, f 1], ![f 0, f 1 + 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge] <;> omega
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![f 0, f 1], ![f 0 + 1, f 1], ?_, ?_, ?_, ?_⟩
    · simp [sharedPrimalEdge] <;> omega
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega


theorem rlc_reflectedCarrierFaces_mem_crossedBoxInterior {n : Int}
    {f g z : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hz : z ∈ sharedPrimalEdge f g)
    (hzBox : z ∈ rect (-2 * n) (2 * n) (-n) n) :
    rlc_dualReflect f ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) ∧
      rlc_dualReflect g ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
  rcases face_adj_dir hfg with rfl | rfl | rfl | rfl
  · have hz' : z = ![f 0 + 1, f 1] ∨
        z = ![f 0 + 1, f 1 + 1] := by
      rw [show sharedPrimalEdge f ![f 0 + 1, f 1] =
          s(![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1]) by
            simpa using sharedPrimalEdge_right (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -(f 0 + 1) - 1 ∧
          -(f 0 + 1) - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega
  · have hz' : z = ![f 0, f 1] ∨ z = ![f 0, f 1 + 1] := by
      rw [show sharedPrimalEdge f ![f 0 - 1, f 1] =
          s(![f 0, f 1], ![f 0, f 1 + 1]) by
            simpa using sharedPrimalEdge_left (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -(f 0 - 1) - 1 ∧
          -(f 0 - 1) - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega
  · have hz' : z = ![f 0, f 1 + 1] ∨
        z = ![f 0 + 1, f 1 + 1] := by
      rw [show sharedPrimalEdge f ![f 0, f 1 + 1] =
          s(![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1]) by
            simpa using sharedPrimalEdge_top (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 + 1 ∧ f 1 + 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega
  · have hz' : z = ![f 0, f 1] ∨ z = ![f 0 + 1, f 1] := by
      rw [show sharedPrimalEdge f ![f 0, f 1 - 1] =
          s(![f 0, f 1], ![f 0 + 1, f 1]) by
            simpa using sharedPrimalEdge_bottom (f 0) (f 1),
        Sym2.mem_iff] at hz
      exact hz
    change
      ((-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 + 1 ∧ f 1 + 1 ≤ n + 1) ∧
        (-2 * n - 1 ≤ -f 0 - 1 ∧ -f 0 - 1 ≤ 2 * n ∧
          -n ≤ f 1 - 1 + 1 ∧ f 1 - 1 + 1 ≤ n + 1))
    rcases hz' with rfl | rfl <;> rw [mem_rect] at hzBox <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzBox <;> omega


theorem rlc_sharedPrimalEdge_mem_crossedBoxImage {n : Int}
    {f g p q : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hp : p ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2))
    (hq : q ∈ rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2)) :
    sharedPrimalEdge f g ∈
      (imageGraph (rlc_connectorCrossedBoxPlanar n)).edgeSet := by
  obtain ⟨p', q', hpq', hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq'] at hshared ⊢
  rw [Sym2.eq_iff] at hshared
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  rcases hshared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨p', hp⟩, ⟨q', hq⟩, hpqAdj, rfl, rfl⟩
  · exact ⟨⟨p', hq⟩, ⟨q', hp⟩, hpqAdj, rfl, rfl⟩


theorem rlc_crossedBox_interiorFace_isolated {n : Int} {f g : Site 2}
    (hf : f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1)) :
    ¬ (whb_faceRegion
      (imageGraph (rlc_connectorCrossedBoxPlanar n))).Adj f g := by
  rintro ⟨hfg, hnot⟩
  have hf' : f ∈ rect (-2 * n - 1) ((2 * n + 1) - 1)
      (-n) ((n + 2) - 1) := by
    rw [mem_rect] at hf ⊢
    omega
  obtain ⟨p, q, hpq, _hpqAdj, hp, hq⟩ :=
    rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect hf' hfg
  exact hnot (rlc_sharedPrimalEdge_mem_crossedBoxImage hfg hpq hp hq)


theorem rlc_crossedBox_interiorFace_component_singleton {n : Int}
    {f g : Site 2}
    (hf : f ∈ rect (-2 * n - 1) (2 * n) (-n) (n + 1))
    (hcomp : (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk f =
      (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk g) :
    f = g := by
  have hreach := ConnectedComponent.exact hcomp
  obtain ⟨w⟩ := hreach
  cases w with
  | nil => rfl
  | cons hadj _ => exact (rlc_crossedBox_interiorFace_isolated hf hadj).elim


end
end StatMech.Universality
