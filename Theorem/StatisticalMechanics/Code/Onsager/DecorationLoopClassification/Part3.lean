/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_mem_decSquarefreeLoopFinset
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    (d : Fin n → ons_Dart L) :
    d ∈ ons_decSquarefreeLoopFinset L a b S ↔
      ons_decLoopExponent L d = ons_finsetExponent S ∧
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) d ≠ 0 := by
  simp [ons_decSquarefreeLoopFinset]

theorem ons_decSquarefreeLoop_eval_zero_injective
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L)) :
    Set.InjOn (fun d : Fin n → ons_Dart L ↦ d 0)
      (ons_decSquarefreeLoopFinset (n := n) L a b S :
        Set (Fin n → ons_Dart L)) := by
  intro d hd e he hzero
  change d ∈ ons_decSquarefreeLoopFinset (n := n) L a b S at hd
  change e ∈ ons_decSquarefreeLoopFinset (n := n) L a b S at he
  rw [ons_mem_decSquarefreeLoopFinset] at hd he
  change d 0 = e 0 at hzero
  let hdvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let hevalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) e he.2
  exact ons_squarefree_valid_loop_eq_of_zero_eq
    L d e hdvalid hevalid S hd.1 he.1 hzero

theorem ons_decLoop_portEdge_injective_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    Function.Injective (fun k : Fin n ↦ ons_portEdge L (d k)) := by
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hexponent
  have hnodup := ons_decWalkExternalDarts_portEdge_nodup q hq
  rw [ons_decLoopWalk_externalDarts L d hvalid] at hnodup
  rw [← List.ofFn_comp'] at hnodup
  have hinjGeom : Function.Injective
      (fun k : Fin n ↦ ons_portEdge L
        (ons_decGeometricLoopStates d k)) :=
    List.nodup_ofFn.mp hnodup
  intro i j hij
  have hgeom : ons_portEdge L
      (ons_decGeometricLoopStates d (-i)) =
      ons_portEdge L (ons_decGeometricLoopStates d (-j)) := by
    simpa [ons_decGeometricLoopStates] using hij
  have hneg : -i = -j := hinjGeom hgeom
  simpa using congrArg Neg.neg hneg

theorem ons_decLoop_dart_ne_rev_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (i j : Fin n) :
    d i ≠ ons_dartRev L (d j) := by
  intro hij
  have hedge : ons_portEdge L (d i) = ons_portEdge L (d j) := by
    rw [hij, ons_portEdge_rev]
  have hindex := ons_decLoop_portEdge_injective_of_squarefree
    L d hvalid S hexponent hedge
  subst j
  exact ons_dartRev_ne_self L (d i) hij.symm

end StatMech.Onsager
