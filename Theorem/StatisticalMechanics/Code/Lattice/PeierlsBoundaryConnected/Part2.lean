/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Def.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem singleton_adj_00_L :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(0:ℤ), 0] ![(-1:ℤ), 0] := by
  have h := latAdj_left (0:ℤ) (0:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(0:ℤ), 0]) (![(-1:ℤ), 0])
      = s(faceCorner00 0 0, faceCorner01 0 0) := by
    have := sharedPrimalEdge_left (0:ℤ) (0:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner01
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  refine ⟨fun _ ⟨_, h2⟩ => by omega, fun _ => ⟨rfl, rfl⟩⟩


theorem singleton_adj_00_B :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have h := latAdj_bottom (0:ℤ) (0:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(0:ℤ), 0]) (![(0:ℤ), -1])
      = s(faceCorner00 0 0, faceCorner10 0 0) := by
    have := sharedPrimalEdge_bottom (0:ℤ) (0:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner10
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  refine ⟨fun _ ⟨_, h2⟩ => by omega, fun _ => ⟨rfl, rfl⟩⟩


theorem singleton_adj_L_LB :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(-1:ℤ), 0] ![(-1:ℤ), -1] := by
  have h := latAdj_bottom (-1:ℤ) (0:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(-1:ℤ), 0]) (![(-1:ℤ), -1])
      = s(faceCorner00 (-1) 0, faceCorner10 (-1) 0) := by
    have := sharedPrimalEdge_bottom (-1:ℤ) (0:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner10
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  rw [show ((-1:ℤ) + 1) = 0 from by ring]
  constructor
  · rintro ⟨h1, _⟩; omega
  · rintro h; exact absurd ⟨rfl, rfl⟩ h


theorem singleton_adj_B_LB :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(0:ℤ), -1] ![(-1:ℤ), -1] := by
  have h := latAdj_left (0:ℤ) (-1:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(0:ℤ), -1]) (![(-1:ℤ), -1])
      = s(faceCorner00 0 (-1), faceCorner01 0 (-1)) := by
    have := sharedPrimalEdge_left (0:ℤ) (-1:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner01
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  rw [show ((-1:ℤ) + 1) = 0 from by ring]
  constructor
  · rintro ⟨h1, _⟩; omega
  · rintro h; exact absurd ⟨rfl, rfl⟩ h


theorem mem_singletonBoundarySupport_00 :
    (![(0:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
  unfold singletonBoundarySupport; simp


theorem singletonBoundarySupport_cases {v : Site 2} (hv : v ∈ singletonBoundarySupport) :
    v = ![(0:ℤ), 0] ∨ v = ![(-1:ℤ), 0] ∨ v = ![(-1:ℤ), -1] ∨ v = ![(0:ℤ), -1] := by
  unfold singletonBoundarySupport at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  tauto


theorem singleton_walk_from_00 {v : Site 2} (hv : v ∈ singletonBoundarySupport) :
    ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
        ![(0:ℤ), 0] v, ∀ w ∈ p.support, w ∈ singletonBoundarySupport := by
  have m00 : (![(0:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  have mL : (![(-1:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  have mLB : (![(-1:ℤ), -1] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  have mB : (![(0:ℤ), -1] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  rcases singletonBoundarySupport_cases hv with rfl | rfl | rfl | rfl
  · 
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact m00
  · 
    refine ⟨SimpleGraph.Walk.cons singleton_adj_00_L SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact m00
    · exact mL
  · 
    refine ⟨SimpleGraph.Walk.cons singleton_adj_00_L
      (SimpleGraph.Walk.cons singleton_adj_L_LB SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact m00
    · exact mL
    · exact mLB
  · 
    refine ⟨SimpleGraph.Walk.cons singleton_adj_00_B SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact m00
    · exact mB


theorem singletonOrigin_faceBoundaryConnected :
    FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
      singletonBoundarySupport := by
  apply faceBoundaryConnected_of_walks ⟨_, mem_singletonBoundarySupport_00⟩
  intro f hf g hg
  obtain ⟨pf, hpf⟩ := singleton_walk_from_00 hf
  obtain ⟨pg, hpg⟩ := singleton_walk_from_00 hg
  
  refine ⟨pf.reverse.append pg, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append] at hw
  rcases List.mem_append.mp hw with hwf | hwg
  · 
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hwf
    exact hpf w hwf
  · 
    exact hpg w (List.mem_of_mem_tail hwg)


theorem support_singletonOrigin_subset :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
      ⊆ (singletonBoundarySupport : Set (Site 2)) := by
  have h := support_faceBoundaryGraph_subset (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
  intro f hf
  have hf' := h hf
  rw [Set.mem_iUnion] at hf'
  obtain ⟨c, hc⟩ := hf'
  rw [Set.mem_iUnion] at hc
  obtain ⟨hcS, hfc⟩ := hc
  rw [Finset.mem_coe, Finset.mem_singleton, origin_eq_zerozero] at hcS
  subst hcS
  unfold cornerFaces at hfc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.coe_insert, Set.mem_insert_iff,
    Finset.coe_singleton, Set.mem_singleton_iff] at hfc
  unfold singletonBoundarySupport
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hfc with h | h | h | h <;> subst h
  · right; right; left; congr 1
  · right; left; congr 1
  · right; right; right; congr 1
  · left; rfl


theorem singletonOrigin_single_dualCircuit :
    ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
        ![(0:ℤ), 0] ![(0:ℤ), 0],
      c.IsTrail ∧
        ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
          e ∈ c.edges :=
  faceBoundaryGraph_single_dualCircuit support_singletonOrigin_subset
    singletonOrigin_faceBoundaryConnected mem_singletonBoundarySupport_00


end Lattice
end StatMech
