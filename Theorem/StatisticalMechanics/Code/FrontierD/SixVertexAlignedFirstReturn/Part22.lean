/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part24
open StatMech.FrontierD


namespace StatMech.FrontierD

theorem flatten_alignedPermOrderedCycleFactorLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedCycleFactorLists sigma).flatten =
      permOrderedAllCycles sigma := by
  unfold alignedPermOrderedCycleFactorLists permOrderedAllCycles List.flatMap
  rfl

theorem alignedPermOrderedCycleFactorLists_chunk_ne_nil
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedCycleFactorLists sigma) :
    chunk ≠ [] := by
  classical
  rw [alignedPermOrderedCycleFactorLists] at hchunk
  obtain ⟨cycle, hcycleList, rfl⟩ := List.mem_map.mp hchunk
  have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
    simpa using hcycleList
  rw [dif_pos hcycle]
  intro hnil
  have hlen : (permOrderedCycleFactor sigma cycle hcycle).length =
      orderOf cycle := by simp [permOrderedCycleFactor]
  rw [hnil] at hlen
  simp only [List.length_nil] at hlen
  exact (orderOf_pos cycle).ne' hlen.symm

theorem permOrderedCycleFactor_getElem_succ
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset)
    (k : Nat)
    (hk : k + 1 < (permOrderedCycleFactor sigma cycle hcycle).length) :
    sigma (permOrderedCycleFactor sigma cycle hcycle)[k] =
      (permOrderedCycleFactor sigma cycle hcycle)[k + 1] := by
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  let enumerate := permCycleFinEquivSupport cycle hc seed
  simp only [permOrderedCycleFactor, List.getElem_ofFn]
  have hkOrder : k < orderOf cycle := by
    simpa [permOrderedCycleFactor] using
      Nat.lt_trans (by omega : k < k + 1) hk
  let i : Fin (orderOf cycle) := ⟨k, hkOrder⟩
  have hi : (enumerate i).1 ∈ cycle.support := (enumerate i).2
  rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2
    (enumerate i).1 hi]
  change cycle ((cycle ^ k) seed.1) = (cycle ^ (k + 1)) seed.1
  rw [show k + 1 = Nat.succ k by omega, pow_succ']
  rfl

theorem permOrderedCycleFactor_getElem_last
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset)
    (hnonempty : permOrderedCycleFactor sigma cycle hcycle ≠ []) :
    sigma ((permOrderedCycleFactor sigma cycle hcycle).getLast hnonempty) =
      (permOrderedCycleFactor sigma cycle hcycle).head hnonempty := by
  have horder : 0 < orderOf cycle := orderOf_pos cycle
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  simp only [permOrderedCycleFactor, List.getElem_ofFn, List.length_ofFn]
  change sigma ((cycle ^ (orderOf cycle - 1)) seed.1) =
    (cycle ^ 0) seed.1
  have hi : (cycle ^ (orderOf cycle - 1)) seed.1 ∈ cycle.support :=
    Equiv.Perm.pow_apply_mem_support.mpr seed.2
  rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2
    ((cycle ^ (orderOf cycle - 1)) seed.1) hi]
  calc
    cycle ((cycle ^ (orderOf cycle - 1)) seed.1) =
        (cycle ^ Nat.succ (orderOf cycle - 1)) seed.1 := by
      rw [pow_succ']
      rfl
    _ = (cycle ^ orderOf cycle) seed.1 := by
      rw [show Nat.succ (orderOf cycle - 1) = orderOf cycle by omega]
    _ = (cycle ^ 0) seed.1 := by rw [pow_orderOf_eq_one]; rfl


end StatMech.FrontierD
