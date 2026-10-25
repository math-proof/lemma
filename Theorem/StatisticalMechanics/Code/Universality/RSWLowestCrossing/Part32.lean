/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part31
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_pathVertices_rot180RightPath {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_pathVertices (rlc_rot180RightPath gamma).1 =
      (rlc_pathVertices gamma.1).image rlc_rot180 := by
  classical
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180RightInducedHom n)
  change w.support.toFinset.image Subtype.val =
    (gamma.1.2.2.1.support.toFinset.image Subtype.val).image rlc_rot180
  ext z
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ List.map (rlc_rot180RightInducedHom n)
        gamma.1.2.2.1.reverse.support := by
      rw [← SimpleGraph.Walk.support_map]
      exact hu
    rw [List.mem_map, SimpleGraph.Walk.support_reverse] at hu'
    obtain ⟨v, hv, huv⟩ := hu'
    refine ⟨(v : Site 2), ⟨v, by simpa using hv, rfl⟩, ?_⟩
    exact congrArg Subtype.val huv
  · rintro ⟨v, ⟨u, hu, huv⟩, hvz⟩
    subst v
    refine ⟨rlc_rot180RightInducedHom n u, ?_, ?_⟩
    · have humap : rlc_rot180RightInducedHom n u ∈
          (gamma.1.2.2.1.reverse.map
            (rlc_rot180RightInducedHom n)).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map,
          SimpleGraph.Walk.support_reverse]
        exact ⟨u, by simpa using hu, rfl⟩
      exact humap
    · exact hvz

theorem rlc_pathVertices_rot180LeftPath {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathVertices (rlc_rot180LeftPath gamma).1 =
      (rlc_pathVertices gamma.1).image rlc_rot180 := by
  classical
  let w := gamma.1.2.2.1.reverse.map (rlc_rot180LeftInducedHom n)
  change w.support.toFinset.image Subtype.val =
    (gamma.1.2.2.1.support.toFinset.image Subtype.val).image rlc_rot180
  ext z
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u ∈ List.map (rlc_rot180LeftInducedHom n)
        gamma.1.2.2.1.reverse.support := by
      rw [← SimpleGraph.Walk.support_map]
      exact hu
    rw [List.mem_map, SimpleGraph.Walk.support_reverse] at hu'
    obtain ⟨v, hv, huv⟩ := hu'
    refine ⟨(v : Site 2), ⟨v, by simpa using hv, rfl⟩, ?_⟩
    exact congrArg Subtype.val huv
  · rintro ⟨v, ⟨u, hu, huv⟩, hvz⟩
    subst v
    refine ⟨rlc_rot180LeftInducedHom n u, ?_, ?_⟩
    · have humap : rlc_rot180LeftInducedHom n u ∈
          (gamma.1.2.2.1.reverse.map
            (rlc_rot180LeftInducedHom n)).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map,
          SimpleGraph.Walk.support_reverse]
        exact ⟨u, by simpa using hu, rfl⟩
      exact humap
    · exact hvz

theorem rlc_pathVertices_rot180_roundtrip_left {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathVertices (rlc_rot180RightPath
      (rlc_rot180LeftPath gamma)).1 = rlc_pathVertices gamma.1 := by
  rw [rlc_pathVertices_rot180RightPath,
    rlc_pathVertices_rot180LeftPath, Finset.image_image]
  simpa [Function.comp_def, rlc_rot180_involutive]

theorem rlc_pathVertices_rot180_roundtrip_right {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_pathVertices (rlc_rot180LeftPath
      (rlc_rot180RightPath gamma)).1 = rlc_pathVertices gamma.1 := by
  rw [rlc_pathVertices_rot180LeftPath,
    rlc_pathVertices_rot180RightPath, Finset.image_image]
  simpa [Function.comp_def, rlc_rot180_involutive]

theorem rlc_pathEdges_rot180RightPath {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_pathEdges (rlc_rot180RightPath gamma).1 =
      (rlc_pathEdges gamma.1).image (Sym2.map rlc_rot180) := by
  classical
  let hom := rlc_rot180RightInducedHom n
  let w := gamma.1.2.2.1.reverse.map hom
  change w.edges.toFinset.image (Sym2.map Subtype.val) =
    (gamma.1.2.2.1.edges.toFinset.image
      (Sym2.map Subtype.val)).image (Sym2.map rlc_rot180)
  have hcomp (d : Sym2 (rect 0 (2 * n) (-n) n)) :
      Sym2.map Subtype.val (Sym2.map hom d) =
        Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := by
    induction d using Sym2.inductionOn with
    | _ u v => rfl
  ext e
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨e0, he0, heq⟩
    have he0' : e0 ∈ List.map (Sym2.map hom)
        gamma.1.2.2.1.reverse.edges := by
      rw [← SimpleGraph.Walk.edges_map]
      exact he0
    rw [List.mem_map, SimpleGraph.Walk.edges_reverse] at he0'
    obtain ⟨d, hd, hde⟩ := he0'
    refine ⟨Sym2.map Subtype.val d,
      ⟨d, by simpa using hd, rfl⟩, ?_⟩
    calc
      Sym2.map rlc_rot180 (Sym2.map Subtype.val d) =
          Sym2.map Subtype.val (Sym2.map hom d) := (hcomp d).symm
      _ = Sym2.map Subtype.val e0 := congrArg (Sym2.map Subtype.val) hde
      _ = e := heq
  · rintro ⟨a, ⟨d, hd, hda⟩, hae⟩
    refine ⟨Sym2.map hom d, ?_, ?_⟩
    · have hdmap : Sym2.map hom d ∈
          (gamma.1.2.2.1.reverse.map hom).edges := by
        rw [SimpleGraph.Walk.edges_map, List.mem_map,
          SimpleGraph.Walk.edges_reverse]
        exact ⟨d, by simpa using hd, rfl⟩
      exact hdmap
    · calc
        Sym2.map Subtype.val (Sym2.map hom d) =
            Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := hcomp d
        _ = Sym2.map rlc_rot180 a := congrArg (Sym2.map rlc_rot180) hda
        _ = e := hae

theorem rlc_pathEdges_rot180LeftPath {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathEdges (rlc_rot180LeftPath gamma).1 =
      (rlc_pathEdges gamma.1).image (Sym2.map rlc_rot180) := by
  classical
  let hom := rlc_rot180LeftInducedHom n
  let w := gamma.1.2.2.1.reverse.map hom
  change w.edges.toFinset.image (Sym2.map Subtype.val) =
    (gamma.1.2.2.1.edges.toFinset.image
      (Sym2.map Subtype.val)).image (Sym2.map rlc_rot180)
  have hcomp (d : Sym2 (rect (-2 * n) 0 (-n) n)) :
      Sym2.map Subtype.val (Sym2.map hom d) =
        Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := by
    induction d using Sym2.inductionOn with
    | _ u v => rfl
  ext e
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨e0, he0, heq⟩
    have he0' : e0 ∈ List.map (Sym2.map hom)
        gamma.1.2.2.1.reverse.edges := by
      rw [← SimpleGraph.Walk.edges_map]
      exact he0
    rw [List.mem_map, SimpleGraph.Walk.edges_reverse] at he0'
    obtain ⟨d, hd, hde⟩ := he0'
    refine ⟨Sym2.map Subtype.val d,
      ⟨d, by simpa using hd, rfl⟩, ?_⟩
    calc
      Sym2.map rlc_rot180 (Sym2.map Subtype.val d) =
          Sym2.map Subtype.val (Sym2.map hom d) := (hcomp d).symm
      _ = Sym2.map Subtype.val e0 := congrArg (Sym2.map Subtype.val) hde
      _ = e := heq
  · rintro ⟨a, ⟨d, hd, hda⟩, hae⟩
    refine ⟨Sym2.map hom d, ?_, ?_⟩
    · have hdmap : Sym2.map hom d ∈
          (gamma.1.2.2.1.reverse.map hom).edges := by
        rw [SimpleGraph.Walk.edges_map, List.mem_map,
          SimpleGraph.Walk.edges_reverse]
        exact ⟨d, by simpa using hd, rfl⟩
      exact hdmap
    · calc
        Sym2.map Subtype.val (Sym2.map hom d) =
            Sym2.map rlc_rot180 (Sym2.map Subtype.val d) := hcomp d
        _ = Sym2.map rlc_rot180 a := congrArg (Sym2.map rlc_rot180) hda
        _ = e := hae

theorem rlc_pathEdges_rot180_roundtrip_left {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_pathEdges (rlc_rot180RightPath
      (rlc_rot180LeftPath gamma)).1 = rlc_pathEdges gamma.1 := by
  rw [rlc_pathEdges_rot180RightPath, rlc_pathEdges_rot180LeftPath,
    Finset.image_image]
  have hinvol : (Sym2.map rlc_rot180 ∘ Sym2.map rlc_rot180) = id := by
    funext e
    induction e using Sym2.inductionOn with
    | _ u v => simp
  rw [hinvol, Finset.image_id]

theorem rlc_swappedRightPathSupport_eq {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    rlc_swappedRightPathSupport gamma =
      crf_swap '' (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : Site 2), ?_, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset]
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact ⟨u, hu, rfl⟩

theorem rlc_swappedLeftPathSupport_eq {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    rlc_swappedLeftPathSupport gamma =
      crf_swap '' (rlc_pathVertices gamma.1 : Set (Site 2)) := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : Site 2), ?_, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset]
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    simp only [rlc_pathVertices, Finset.mem_coe, Finset.mem_image,
      List.mem_toFinset] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact ⟨u, hu, rfl⟩


theorem rlc_belowSet_boundary_path {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rect 0 (2 * n) (-n) n)
    (hv : v ∈ rect 0 (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_belowSet hn gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  have hbdSwap : bdEdge (rlc_swappedBelowSet hn gamma)
      s(crf_swap u, crf_swap v) := by
    rw [bdEdge_mk] at hbd ⊢
    simpa [rlc_belowSet] using hbd
  have h := (rlc_swappedBelowSet_spec hn gamma).2.2
    (crf_swap u) (crf_swap v)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n u).mp hu)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n v).mp hv)
    ((crf_adj_swap u v).mp hadj) hbdSwap
  rw [rlc_swappedRightPathSupport_eq] at h
  rcases h with ⟨z, hz, hzu⟩ | ⟨z, hz, hzv⟩
  · left
    exact crf_swap.injective hzu |>.symm ▸ hz
  · right
    exact crf_swap.injective hzv |>.symm ▸ hz


theorem rlc_aboveSet_boundary_path {n : ℤ} (hn : 0 < n)
    (gamma : RlcLeftDiagonalPath n) {u v : Site 2}
    (hu : u ∈ rect (-2 * n) 0 (-n) n)
    (hv : v ∈ rect (-2 * n) 0 (-n) n)
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (rlc_aboveSet hn gamma) s(u, v)) :
    u ∈ rlc_pathVertices gamma.1 ∨ v ∈ rlc_pathVertices gamma.1 := by
  have hbdSwap : bdEdge (rlc_swappedLeftBelowSet hn gamma)
      s(crf_swap u, crf_swap v) := by
    rw [bdEdge_mk] at hbd ⊢
    simp only [rlc_aboveSet, Set.mem_preimage, Set.mem_compl_iff] at hbd
    tauto
  have h := (rlc_swappedLeftBelowSet_spec hn gamma).2.2
    (crf_swap u) (crf_swap v)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n u).mp hu)
    ((crf_mem_rect_swap (-2 * n) 0 (-n) n v).mp hv)
    ((crf_adj_swap u v).mp hadj) hbdSwap
  rw [rlc_swappedLeftPathSupport_eq] at h
  rcases h with ⟨z, hz, hzu⟩ | ⟨z, hz, hzv⟩
  · left
    exact crf_swap.injective hzu |>.symm ▸ hz
  · right
    exact crf_swap.injective hzv |>.symm ▸ hz


end Universality
end StatMech
