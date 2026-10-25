/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part6


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


@[simp] theorem kwCyclicIntegralVertex_fin
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    kwCyclicIntegralVertex p i.val = p i := by
  unfold kwCyclicIntegralVertex
  congr
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem kwCyclicIntegralVertex_succ
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    kwCyclicIntegralVertex p (i.val + 1) = p (i + 1) := by
  unfold kwCyclicIntegralVertex
  congr 1
  apply Fin.ext
  rw [Fin.val_add, Fin.val_one']
  simpa [Nat.mod_eq_of_lt i.isLt] using Nat.add_mod i.val 1 n

theorem kwIndexedPrefixBlocks_integralPolygon
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    kwIndexedPrefixBlocks (kwCyclicIntegralVertex p)
        (List.ofFn (kwIntegralPolygonEdgeWord p)) =
      kwIntegralPolygonPointList p := by
  unfold kwIndexedPrefixBlocks kwIntegralPolygonPointList
  rw [List.mapIdx_eq_ofFn]
  simp only [List.length_ofFn, List.get_ofFn]
  apply congrArg List.flatten
  rw [List.ofFn_inj]
  funext i
  simp [kwIntegralPolygonEdgePoints]


theorem kwIntegralPolygonPointList_eq_prefixPositions
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    kwIntegralPolygonPointList p =
      (kwPrefixPositions (kwIntegralPolygonWord p)).map (p 0 + ·) := by
  symm
  rw [kwIntegralPolygonWord]
  have hstep : ∀ k
      (hk : k < (List.ofFn (kwIntegralPolygonEdgeWord p)).length),
      ((((List.ofFn (kwIntegralPolygonEdgeWord p))[k]'hk).map stepOf).sum) =
        kwCyclicIntegralVertex p (k + 1) -
          kwCyclicIntegralVertex p k := by
    intro k hk
    have hkn : k < n := by simpa using hk
    let i : Fin n := ⟨k, hkn⟩
    simp only [List.getElem_ofFn]
    change ((kwIntegralPolygonEdgeWord p i).map stepOf).sum = _
    rw [kwIntegralPolygonEdgeWord_step_sum]
    change p (i + 1) - p i = _
    rw [← kwCyclicIntegralVertex_succ p i,
      ← kwCyclicIntegralVertex_fin p i]
  have hzero : kwCyclicIntegralVertex p 0 = p 0 := by
    simpa using kwCyclicIntegralVertex_fin p (0 : Fin n)
  calc
    (kwPrefixPositions (List.ofFn
          (kwIntegralPolygonEdgeWord p)).flatten).map (p 0 + ·) =
        (kwPrefixPositions (List.ofFn
          (kwIntegralPolygonEdgeWord p)).flatten).map
            (kwCyclicIntegralVertex p 0 + ·) := by rw [hzero]
    _ = kwIndexedPrefixBlocks (kwCyclicIntegralVertex p)
          (List.ofFn (kwIntegralPolygonEdgeWord p)) :=
      kwPrefixPositions_flatten_map (kwCyclicIntegralVertex p)
        (List.ofFn (kwIntegralPolygonEdgeWord p)) hstep
    _ = kwIntegralPolygonPointList p :=
      kwIndexedPrefixBlocks_integralPolygon p


theorem kwIntegralPolygonPointList_nodup
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    (kwIntegralPolygonPointList p).Nodup := by
  rw [kwIntegralPolygonPointList, List.nodup_flatten]
  constructor
  · intro points hpoints
    rw [List.mem_ofFn] at hpoints
    obtain ⟨i, rfl⟩ := hpoints
    exact kwIntegralPolygonEdgePoints_nodup_of_axis p i (haxis i)
  · rw [List.pairwise_ofFn]
    intro i j hij
    rw [List.disjoint_left]
    intro q hqi hqj
    have hi := kwIntegralPolygonEdgePoints_complex_mem_halfOpen
      p i (haxis i) hqi
    have hj := kwIntegralPolygonEdgePoints_complex_mem_halfOpen
      p j (haxis j) hqj
    exact Set.disjoint_left.mp
      (hsimple.halfOpenEdge_disjoint (Fin.ne_of_lt hij)) hi hj


theorem kwIntegralPolygonWord_vertexCount_le_length
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    n ≤ (kwIntegralPolygonWord p).length := by
  have hedge (i : Fin n) :
      1 ≤ (kwIntegralPolygonEdgeWord p i).length := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.ne_of_gt
    apply List.length_pos_of_ne_nil
    apply kwIntegralAxisWord_ne_nil
    rw [sub_ne_zero]
    intro hpi
    apply hsimple.edge_ne_zero i
    unfold kwRawEdge
    simpa [hpi]
  rw [kwIntegralPolygonWord, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  calc
    n = ∑ _ : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, (kwIntegralPolygonEdgeWord p i).length := by
      exact Finset.sum_le_sum fun i _ ↦ hedge i


theorem kwIntegralPolygonDirection_pos_injective
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    [NeZero (kwIntegralPolygonWord p).length]
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    Function.Injective (pos (kwIntegralPolygonDirection p)) := by
  have hpoints := kwIntegralPolygonPointList_nodup p haxis hsimple
  rw [kwIntegralPolygonPointList_eq_prefixPositions] at hpoints
  have hprefix :
      (kwPrefixPositions (kwIntegralPolygonWord p)).Nodup :=
    hpoints.of_map (p 0 + ·)
  change Function.Injective
    (pos (kwListDirection (kwIntegralPolygonWord p)))
  exact kwListDirection_pos_injective_of_prefixPositions_nodup _ hprefix


theorem kwIntegralPolygonDirection_phaseProduct_eq_neg_one
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    [NeZero (kwIntegralPolygonWord p).length]
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    (∏ k : Fin (kwIntegralPolygonWord p).length,
      kwVectorTurnPhase
        (kwRectilinearVector (kwIntegralPolygonDirection p k))
        (kwRectilinearVector
          (kwIntegralPolygonDirection p (k + 1)))) = -1 := by
  have hclosed := kwIntegralPolygonDirection_closed p
  have hinj := kwIntegralPolygonDirection_pos_injective p haxis hsimple
  have hlen : 3 ≤ (kwIntegralPolygonWord p).length :=
    hsimple.three_le.trans
      (kwIntegralPolygonWord_vertexCount_le_length p hsimple)
  have hnu := StatMech.Onsager.ons_nonUturn_of_pos_injective
    (kwIntegralPolygonDirection p) hclosed hinj hlen
  exact kwRectilinearVector_phaseProduct_eq_neg_one
    (kwIntegralPolygonDirection p) hclosed hinj hlen hnu


end StatMech.FrontierA
