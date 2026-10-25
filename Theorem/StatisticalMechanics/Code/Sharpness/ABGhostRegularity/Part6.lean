/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Def.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part5
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem abgrActive_merge_eq (o : V)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    abgrActive (G := G) o
        (abgrMerge (FieldGhostDict.ghostEdges V) gamma eta) =
      abgrActive (G := G) o
        (abgrMerge (FieldGhostDict.ghostEdges V) (fun _ => false) eta) := by
  unfold abgrActive
  rw [abgrCloseGhost_merge_eq gamma eta]
  rw [abgrCloseGhost_merge_eq (fun _ => false) eta]


theorem abgr_section_iff_anyOpen (o : V)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈
        connEvent (withGhost G) Set.univ (some o) {none} ↔
      ∃ e ∈ abgrActiveGhost G o eta, gamma e = true := by
  rw [abgr_connEvent_iff_exists_active G o]
  constructor
  · rintro ⟨x, hx, hopen⟩
    rw [abgrActive_merge_eq G o gamma eta] at hx
    refine ⟨abgrGhostEdgeEquiv (V := V) x, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · rw [← abgrMerge_mem (FieldGhostDict.ghostEdges V) gamma eta
          (abgrGhostEdgeEquiv (V := V) x)]
      simpa only [abgrGhostEdgeEquiv_apply] using hopen
  · rintro ⟨e, he, hopen⟩
    rw [abgrActiveGhost, Finset.mem_map] at he
    obtain ⟨x, hx, hxe⟩ := he
    subst e
    refine ⟨x, ?_, ?_⟩
    · rwa [abgrActive_merge_eq G o gamma eta]
    · calc
        abgrMerge (FieldGhostDict.ghostEdges V) gamma eta s(some x, none) =
            gamma (abgrGhostEdgeEquiv (V := V) x) := by
              rw [← abgrGhostEdgeEquiv_apply x]
              exact abgrMerge_mem (FieldGhostDict.ghostEdges V) gamma eta
                (abgrGhostEdgeEquiv (V := V) x)
        _ = true := hopen


theorem abgr_abfaMag_eq_cluster_mixture (J : Sym2 V -> Real) (o : V)
    (beta h : Real) :
    abfaMag G J o beta h =
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        (∏ e : {e // e ∉ FieldGhostDict.ghostEdges V},
          if eta e then pBeta (abfaLiftCoupling G J e) beta
          else 1 - pBeta (abfaLiftCoupling G J e) beta) *
        (1 - (1 - qField h) ^ (abgrActiveGhost G o eta).card) := by
  unfold abfaMag abfaParams abpdBetaFieldParams
  rw [abgr_probV_split]
  apply Finset.sum_congr rfl
  intro eta _
  congr 1
  have hset :
      {gamma : {e // e ∈ FieldGhostDict.ghostEdges V} -> Bool |
          abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈
            connEvent (withGhost G) Set.univ (some o) {none}} =
        {gamma | ∃ e ∈ abgrActiveGhost G o eta, gamma e = true} := by
    ext gamma
    exact abgr_section_iff_anyOpen G o gamma eta
  rw [hset, abgr_probV_anyOpen]
  simp


end Sharpness
end StatMech
