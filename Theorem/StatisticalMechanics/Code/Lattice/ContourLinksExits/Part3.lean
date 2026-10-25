/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part3
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem dartFace_of_dir_right (e : Dart) (hd : e.dir = ![1, 0]) :
    dartFace e = ![e.tail 0, e.tail 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> simp [rot90Fun, negPart]


theorem dartFace_of_dir_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1 - 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> (simp [rot90Fun, negPart]; ring)


theorem dartFace_of_dir_up (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace e = ![e.tail 0 - 1, e.tail 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> simp [rot90Fun, negPart] <;> try ring


theorem dartFace_of_dir_down (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace e = ![e.tail 0, e.tail 1 - 1] := by
  unfold dartFace; rw [hd]; funext i; fin_cases i <;> simp [rot90Fun, negPart] <;> try ring


theorem dartFace_exitDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    dartFace (exitDart (ω := ω) hfin) = exitFaceUp (ω := ω) hfin := by
  rw [dartFace_of_dir_right _ (exitDart_dir (ω := ω) hfin)]
  show (![axisSite (exitIndex (ω := ω) hfin) 0, axisSite (exitIndex (ω := ω) hfin) 1] : Site 2)
      = exitFaceUp (ω := ω) hfin
  unfold exitFaceUp
  funext i; fin_cases i <;> simp [axisSite]


theorem dartFace_leftExitDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    dartFace (leftExitDart (ω := ω) hfin) = leftExitFaceDown (ω := ω) hfin := by
  rw [dartFace_of_dir_left _ (leftExitDart_dir (ω := ω) hfin)]
  show (![leftAxisSite (leftExitIndex (ω := ω) hfin) 0 - 1,
        leftAxisSite (leftExitIndex (ω := ω) hfin) 1 - 1] : Site 2)
      = leftExitFaceDown (ω := ω) hfin
  unfold leftExitFaceDown
  funext i; fin_cases i <;> simp [leftAxisSite]


theorem dartFace_leftExitDart_coord0_nonpos (hfin : (cluster 2 ω (origin 2)).Finite) :
    dartFace (leftExitDart (ω := ω) hfin) 0 ≤ 0 := by
  rw [dartFace_leftExitDart (ω := ω) hfin]
  exact leftExitFaceDown_coord0_nonpos (ω := ω) hfin


theorem faceBoundaryGraph_adj_vert (K : Set (Site 2)) (a b : ℤ)
    (h : ((![a, b] : Site 2) ∈ K) ↔ ((![a + 1, b] : Site 2) ∉ K)) :
    (faceBoundaryGraph K).Adj ![a, b] ![a, b - 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_bottom a b, ?_⟩
  rw [sharedPrimalEdge_bottom a b, bdEdge_mk]
  unfold faceCorner00 faceCorner10
  exact h


theorem faceBoundaryGraph_adj_horiz (K : Set (Site 2)) (a b : ℤ)
    (h : ((![a, b] : Site 2) ∈ K) ↔ ((![a, b + 1] : Site 2) ∉ K)) :
    (faceBoundaryGraph K).Adj ![a, b] ![a - 1, b] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_left a b, ?_⟩
  rw [sharedPrimalEdge_left a b, bdEdge_mk]
  unfold faceCorner00 faceCorner01
  exact h


theorem dart_head_eq (e : Dart) : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel


theorem dartFace_next_of_dir_right (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![1, 0]) :
    dartFace (dartNext K e) = ![e.tail 0, e.tail 1 - 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![0, -1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![0, 1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0 + 1, e.tail 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_up _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_right _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_down _ (by rw [mkDart_dir, ht]),
        mkDart_tail]


theorem dartFace_next_of_dir_left (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![-1, 0]) :
    dartFace (dartNext K e) = ![e.tail 0 - 1, e.tail 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![0, 1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![0, -1] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0 - 1, e.tail 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_down _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_left _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_up _ (by rw [mkDart_dir, ht]),
        mkDart_tail]


theorem dartFace_next_of_dir_up (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![0, 1]) :
    dartFace (dartNext K e) = ![e.tail 0, e.tail 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![-1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0, e.tail 1 + 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_left _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_up _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_right _ (by rw [mkDart_dir, ht]),
        mkDart_tail]


theorem dartFace_next_of_dir_down (K : Set (Site 2)) (e : Dart) (hd : e.dir = ![0, -1]) :
    dartFace (dartNext K e) = ![e.tail 0 - 1, e.tail 1 - 1] := by
  classical
  have ht : (-rot90Fun e.dir : Site 2) = ![-1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hr : (rot90Fun e.dir : Site 2) = ![1, 0] := by
    rw [hd]; funext i; fin_cases i <;> simp [rot90Fun]
  have hhead : e.head = ![e.tail 0, e.tail 1 - 1] := by
    rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K e hA, dartFace_of_dir_right _ (by rw [mkDart_dir, hr]),
      mkDart_tail, ht, hhead]
    funext i; fin_cases i <;> simp <;> try ring
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K e hA hB, dartFace_of_dir_down _ (by rw [mkDart_dir, hd]),
        mkDart_tail, ht]
      funext i; fin_cases i <;> simp <;> try ring
    · rw [dartNext_of_corner K e hA hB, dartFace_of_dir_left _ (by rw [mkDart_dir, ht]),
        mkDart_tail]


theorem dartFace_step_adj (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (faceBoundaryGraph K).Adj (dartFace e) (dartFace (dartNext K e)) := by
  obtain ⟨htail, hhead⟩ := he
  rcases dartDir_cases e with hd | hd | hd | hd
  · 
    rw [dartFace_of_dir_right e hd, dartFace_next_of_dir_right K e hd]
    have hh : e.head = ![e.tail 0 + 1, e.tail 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
    refine faceBoundaryGraph_adj_vert K (e.tail 0) (e.tail 1) ?_
    constructor
    · intro _; rw [hh] at hhead; exact hhead
    · intro _; show (![e.tail 0, e.tail 1] : Site 2) ∈ K
      have : (![e.tail 0, e.tail 1] : Site 2) = e.tail := by funext i; fin_cases i <;> rfl
      rw [this]; exact htail
  · 
    rw [dartFace_of_dir_left e hd, dartFace_next_of_dir_left K e hd]
    have hh : e.head = ![e.tail 0 - 1, e.tail 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
    
    have key : (faceBoundaryGraph K).Adj ![e.tail 0 - 1, e.tail 1]
        ![e.tail 0 - 1, e.tail 1 - 1] := by
      refine faceBoundaryGraph_adj_vert K (e.tail 0 - 1) (e.tail 1) ?_
      constructor
      · intro hin; exact absurd (by
          have : (![e.tail 0 - 1, e.tail 1] : Site 2) = e.head := hh.symm
          rw [this] at hin; exact hin) hhead
      · intro hout
        exact absurd (by
          have : (![e.tail 0 - 1 + 1, e.tail 1] : Site 2) = e.tail := by
            funext i; fin_cases i <;> simp <;> ring
          rw [this]; exact htail) hout
    exact key.symm
  · 
    rw [dartFace_of_dir_up e hd, dartFace_next_of_dir_up K e hd]
    have hh : e.head = ![e.tail 0, e.tail 1 + 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp
    have key : (faceBoundaryGraph K).Adj ![e.tail 0, e.tail 1] ![e.tail 0 - 1, e.tail 1] := by
      refine faceBoundaryGraph_adj_horiz K (e.tail 0) (e.tail 1) ?_
      constructor
      · intro _; rw [hh] at hhead; exact hhead
      · intro _; show (![e.tail 0, e.tail 1] : Site 2) ∈ K
        have : (![e.tail 0, e.tail 1] : Site 2) = e.tail := by funext i; fin_cases i <;> rfl
        rw [this]; exact htail
    exact key.symm
  · 
    rw [dartFace_of_dir_down e hd, dartFace_next_of_dir_down K e hd]
    have hh : e.head = ![e.tail 0, e.tail 1 - 1] := by
      rw [dart_head_eq e, hd]; funext i; fin_cases i <;> simp <;> ring
    refine faceBoundaryGraph_adj_horiz K (e.tail 0) (e.tail 1 - 1) ?_
    constructor
    · intro hin
      exact absurd (by
        have : (![e.tail 0, e.tail 1 - 1] : Site 2) = e.head := by rw [hh]
        rw [this] at hin; exact hin) hhead
    · intro hout
      exact absurd (by
        have : (![e.tail 0, e.tail 1 - 1 + 1] : Site 2) = e.tail := by
          funext i; fin_cases i <;> simp <;> ring
        rw [this]; exact htail) hout


theorem iterate_isBoundaryDart (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    IsBoundaryDart K ((dartNext K)^[n] e) := by
  induction n with
  | zero => simpa using he
  | succ m ih => rw [Function.iterate_succ_apply']; exact dartNext_isBoundaryDart K _ ih


theorem dartFace_iterate_reachable (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) :
    (faceBoundaryGraph K).Reachable (dartFace e) (dartFace ((dartNext K)^[n] e)) := by
  induction n with
  | zero => simpa using SimpleGraph.Reachable.refl (dartFace e)
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine ih.trans ?_
    exact (dartFace_step_adj K _ (iterate_isBoundaryDart K e he m)).reachable


theorem dartFace_reachable_of_orbit (K : Set (Site 2)) (e f : Dart) (he : IsBoundaryDart K e)
    {n : ℕ} (hf : (dartNext K)^[n] e = f) :
    (faceBoundaryGraph K).Reachable (dartFace e) (dartFace f) := by
  rw [← hf]; exact dartFace_iterate_reachable K e he n


end Lattice
end StatMech
