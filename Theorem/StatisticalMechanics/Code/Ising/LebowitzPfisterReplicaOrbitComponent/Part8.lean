/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part7
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaPartialReflectCopyEquivRaw_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaPartialReflectCopyEquivRaw G sites m P c).1 =
      if c ∈ P then lpReplicaCurrentEdgeReflect G sites c.1 else c.1 := by
  classical
  by_cases hc : c ∈ P
  · simp [lpReplicaPartialReflectCopyEquivRaw, hc,
      lpReplicaCopySubsetEquivProfile,
      lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl,
      lpReplicaCollisionCopyEquiv,
      lpReplicaReflectCopyEquiv]
    rfl
  · simp [lpReplicaPartialReflectCopyEquivRaw, hc,
      lpReplicaCopySubsetEquivProfile,
      lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl,
      lpReplicaCollisionCopyEquiv,
      lpReplicaReflectCopyEquiv]
    rfl

set_option maxHeartbeats 800000 in


theorem lpReplicaPartialReflectCopyEquivRaw_index_of_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∈ P) :
    (lpReplicaPartialReflectCopyEquivRaw G sites m P c).2.val =
      profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)
          (lpReplicaCurrentEdgeReflect G sites c.1) +
        (((lpReplicaCopyIndicesAtEdge G sites m P c.1).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m P c.1)).symm
            ⟨c.2, by
              simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
                Finset.mem_univ, true_and] using hc⟩).val := by
  classical
  unfold lpReplicaPartialReflectCopyEquivRaw
  dsimp only [Equiv.trans_apply]
  have hsplit : (Equiv.sumCompl (fun d : Copy
      (lpReplicaCurrentGraph G sites) m => d ∈ P)).symm c =
      Sum.inl (⟨c, hc⟩ : {d : Copy
        (lpReplicaCurrentGraph G sites) m // d ∈ P}) := by
    simp [Equiv.sumCompl, hc]
  rw [hsplit]
  rfl

set_option maxHeartbeats 800000 in


theorem lpReplicaPartialReflectCopyEquivRaw_index_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) (hc : c ∉ P) :
    (lpReplicaPartialReflectCopyEquivRaw G sites m P c).2.val =
        (((lpReplicaCopyIndicesAtEdge G sites m (Finset.univ \ P) c.1).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m
            (Finset.univ \ P) c.1)).symm
            ⟨c.2, by
              simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
                Finset.mem_univ, Finset.mem_sdiff, true_and] using hc⟩).val := by
  classical
  unfold lpReplicaPartialReflectCopyEquivRaw
  dsimp only [Equiv.trans_apply]
  have hsplit : (Equiv.sumCompl (fun d : Copy
      (lpReplicaCurrentGraph G sites) m => d ∈ P)).symm c =
      Sum.inr (⟨c, hc⟩ : {d : Copy
        (lpReplicaCurrentGraph G sites) m // d ∉ P}) := by
    simp [Equiv.sumCompl, hc]
  rw [hsplit]
  rfl


end
end StatMech.Ising
