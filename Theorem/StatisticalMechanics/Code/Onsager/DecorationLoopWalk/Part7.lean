/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part6


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decLoopWalk_snd
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    (ons_decLoopWalk L d hvalid).snd = ons_dartRev L (d 0) := by
  unfold ons_decLoopWalk
  dsimp only
  change ((ons_decWalkOfKWChain L (d 0)
      ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) _).copy _ _).getVert 1 = _
  rw [SimpleGraph.Walk.getVert_copy]
  apply ons_decWalkOfKWChain_snd_of_ne_nil
  simp

theorem ons_decLoopWalk_externalDarts
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decWalkExternalDarts (ons_decLoopWalk L d hvalid) =
      List.ofFn (ons_decGeometricLoopStates d) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  unfold ons_decLoopWalk
  simp only [ons_decWalkExternalDarts, SimpleGraph.Walk.darts_copy]
  change ons_decWalkExternalDarts
      (ons_decWalkOfKWChain L (d 0)
        ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) _) = _
  rw [ons_decWalkOfKWChain_externalDarts]
  rw [← List.cons_append]
  have hhead :
      d 0 :: (List.ofFn (ons_decGeometricLoopStates d)).tail =
        List.ofFn (ons_decGeometricLoopStates d) := by
    rw [List.ofFn_succ]
    simp [ons_decGeometricLoopStates]
  rw [hhead, List.dropLast_concat]

theorem ons_decLoopWalk_cycleDartList
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decCycleDartList (ons_decLoopWalk L d hvalid) =
      List.ofFn d := by
  rw [ons_decCycleDartList_eq, ons_decLoopWalk_externalDarts]
  exact ons_decGeometricLoopStates_tail_reverse d

theorem ons_decLoopWalk_cycleDartLoop
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (k : Fin n) :
    ons_decCycleDartLoop (ons_decLoopWalk L d hvalid)
        ⟨k.val, by
          rw [ons_decLoopWalk_cycleDartList, List.length_ofFn]
          exact k.isLt⟩ =
      d k := by
  unfold ons_decCycleDartLoop
  simp [ons_decLoopWalk_cycleDartList]

theorem ons_decLoopWalk_edgeCount
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decWalkEdgeCount (ons_decLoopWalk L d hvalid) =
      ons_decLoopExponent L d := by
  unfold ons_decLoopWalk
  simp only [ons_decWalkEdgeCount, SimpleGraph.Walk.edges_copy]
  change ons_decWalkEdgeCount
      (ons_decWalkOfKWChain L (d 0)
        ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) _) = _
  rw [ons_decWalkOfKWChain_edgeCount]
  calc
    ons_decKWChainExponent L (d 0)
        ((List.ofFn (ons_decGeometricLoopStates d)).tail ++ [d 0]) =
        ∑ k : Fin n, ons_decTransitionExponent L
          (ons_decGeometricLoopStates d (k + 1))
          (ons_decGeometricLoopStates d k) := by
      simpa [ons_decGeometricLoopStates] using
        ons_decKWChainExponent_closed_eq_sum L
          (ons_decGeometricLoopStates d)
    _ = ons_decLoopExponent L d :=
      ons_decGeometricLoopStates_sum_exponent d

theorem ons_decLoopWalk_isTrail_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopWalk L d hvalid).IsTrail := by
  rw [SimpleGraph.Walk.isTrail_def]
  apply List.nodup_iff_count_le_one.mpr
  intro edge
  have hcount := DFunLike.congr_fun
    (ons_decLoopWalk_edgeCount L d hvalid) edge
  unfold ons_decWalkEdgeCount at hcount
  rw [Multiset.toFinsupp_apply, hexponent,
    ons_finsetExponent_apply] at hcount
  by_cases hedge : edge ∈ S
  · rw [if_pos hedge] at hcount
    rw [Multiset.coe_count] at hcount
    omega
  · rw [if_neg hedge] at hcount
    rw [Multiset.coe_count] at hcount
    omega

theorem ons_decLoopWalk_ne_nil
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopWalk L d hvalid ≠ .nil := by
  intro hnil
  have hcount := ons_decLoopWalk_edgeCount L d hvalid
  rw [hnil] at hcount
  change (0 : ons_DecEdge L →₀ ℕ) = ons_decLoopExponent L d at hcount
  have hdegree := ons_decLoopExponent_length_le L d
  rw [← hcount] at hdegree
  simp [ons_finsuppTotalDegree] at hdegree
  exact (NeZero.ne n) hdegree

theorem ons_decLoopWalk_isCycle_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopWalk L d hvalid).IsCycle := by
  apply ons_closed_trail_isCycle_of_degree_le_three (ons_decGraph L)
  · exact ons_decLoopWalk_isTrail_of_squarefree L d hvalid S hexponent
  · exact ons_decLoopWalk_ne_nil L d hvalid
  · exact ons_decGraph_degree_le_three L

theorem ons_decLoopWalk_edges_toFinset_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopWalk L d hvalid).edges.toFinset = S := by
  apply ons_finsetExponent_injective
  rw [ons_finsetExponent_toFinset_eq_edgeCount _
    ((ons_decLoopWalk_isTrail_of_squarefree
      L d hvalid S hexponent).edges_nodup)]
  change ons_decWalkEdgeCount (ons_decLoopWalk L d hvalid) = _
  rw [ons_decLoopWalk_edgeCount, hexponent]

theorem ons_decLoop_valid_of_scalar_ne_zero
    (L : ℕ) (omega u v : ℂ) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hscalar : ons_decLoopScalar L omega u v d ≠ 0) :
    ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1 := by
  intro k
  have hfactor :
      ons_decTransitionScalar L omega u v (d k) (d (k + 1)) ≠ 0 := by
    intro hzero
    apply hscalar
    unfold ons_decLoopScalar
    exact Finset.prod_eq_zero (Finset.mem_univ k) hzero
  unfold ons_decTransitionScalar at hfactor
  by_contra hstep
  rw [if_neg hstep] at hfactor
  exact hfactor rfl

theorem ons_decLoopScalar_eq_loopWeight_one
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    ons_decLoopScalar L omega u v d =
      ons_loopWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v) d := by
  have hspecialized :
      ons_decSpecializedWeight (fun _ : Sym2 (ZMod L × ZMod L) ↦ (1 : ℂ)) =
        (fun _ : ons_DecEdge L ↦ (1 : ℂ)) := by
    funext edge
    classical
    unfold ons_decSpecializedWeight
    split <;> rfl
  have hmatrix := ons_KWmatDecorationWeightedPhase_specialized
    L (fun _ : Sym2 (ZMod L × ZMod L) ↦ (1 : ℂ)) omega u v
  rw [hspecialized] at hmatrix
  have hloop := ons_loopWeight_KWmatDecorationWeightedPhase
    (L := L) (fun _ : ons_DecEdge L ↦ (1 : ℂ)) omega u v d
  rw [hmatrix] at hloop
  simpa using hloop.symm

theorem ons_decLoopScalar_eq_cycleFirstReturn
    (L : ℕ) [Fact (2 < L)] (omega u v : ℂ)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ons_decLoopScalar L omega u v d =
      ons_edgeWeight
        (ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v)
        (ons_decCycleFirstReturn (ons_decLoopWalk L d hvalid)) := by
  let q := ons_decLoopWalk L d hvalid
  let Lambda := ons_KWmatWeightedPhase L (fun _ ↦ 1) omega u v
  rw [ons_decLoopScalar_eq_loopWeight_one]
  calc
    ons_loopWeight Lambda d =
        ons_edgeWeight Lambda (List.ofFn d ++ [d 0]) :=
      ons_loopWeight_eq_edgeWeight_neZero Lambda d
    _ = ons_edgeWeight Lambda
        (List.ofFn (ons_decCycleDartLoop q) ++
          [ons_decCycleDartLoop q 0]) := by
      rw [ons_decCycleDartLoop_zero,
        ons_decCycleDartList_ofFn,
        ons_decLoopWalk_cycleDartList]
    _ = ons_loopWeight Lambda (ons_decCycleDartLoop q) :=
      (ons_loopWeight_eq_edgeWeight_neZero Lambda
        (ons_decCycleDartLoop q)).symm
    _ = ons_edgeWeight Lambda (ons_decCycleFirstReturn q) :=
      (ons_decCycleFirstReturn_edgeWeight_eq_loopWeight q Lambda).symm

theorem ons_decLoopScalar_eq_neg_spinCharacter_of_squarefree
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (hscalar : ons_decLoopScalar L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) d =
      -((ons_spinCharacter a b
        (ons_evenHomology L
          (ons_walkOriginalEdges
            (ons_decLoopWalk L d
              (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b) d hscalar))))) : ℂ) := by
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hscalar
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hexponent
  have hsnd : q.snd = ons_dartRev L (d 0) :=
    ons_decLoopWalk_snd L d hvalid
  rw [ons_decLoopScalar_eq_cycleFirstReturn L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hvalid]
  simpa [q, hvalid] using
    ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
      q hq hsnd (fun _ ↦ 1) a b

end StatMech.Onsager
