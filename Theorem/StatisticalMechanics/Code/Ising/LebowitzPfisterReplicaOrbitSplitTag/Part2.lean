/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSplitTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaTagEquiv
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitCollisionSplitEquiv_symm_left
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (d : Copy (lpReplicaCurrentGraph G sites) a) :
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm
        (lpReplicaCollisionLeftCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a) d) =
      ((lpReplicaCopySubsetEquivProfile G sites m P).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites)) hP.symm) d)).1 := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let b := lpReplicaReflectedResidual G sites m a
  let leftEquiv :=
    (lpReplicaCopySubsetEquivProfile G sites m P).trans
      (Equiv.cast (congrArg (Copy H) hP))
  let rightEquiv :=
    (lpReplicaCopyNotMemEquivCompl G sites m P).trans
      ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).trans
        (Equiv.cast (congrArg (Copy H)
          (lpReplicaCollisionSplit_complProfile G sites m a P hP))))
  let split : Copy H m ≃ Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr leftEquiv rightEquiv)
  let collide : Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) ≃
      Copy H (lpReplicaCollisionProfile G sites a b) :=
    (Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (b (lpReplicaCurrentEdgeReflect G sites e)))).symm |>.trans
      (lpReplicaCollisionCopyEquiv G sites a b)
  change (split.trans collide).symm
      (lpReplicaCollisionLeftCopyEmbedding G sites a b d) = _
  rw [Equiv.symm_trans_apply]
  have hcollide : collide.symm
      (lpReplicaCollisionLeftCopyEmbedding G sites a b d) = Sum.inl d := by
    apply collide.injective
    rw [collide.apply_symm_apply]
    rfl
  rw [hcollide]
  simp [split, leftEquiv]
  cases hP
  rfl


theorem lpReplicaOrbitCollisionSplitEquiv_symm_right
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaReflectedResidual G sites m a)) :
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP).symm
        (lpReplicaCollisionRightCopyEmbedding G sites a
          (lpReplicaReflectedResidual G sites m a) d) =
      ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
          (lpReplicaCollisionSplit_complProfile G sites m a P hP).symm)
          (lpReplicaReflectCopyEquiv G sites
            (lpReplicaReflectedResidual G sites m a) d))).1 := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let b := lpReplicaReflectedResidual G sites m a
  let hcompl := lpReplicaCollisionSplit_complProfile G sites m a P hP
  let leftEquiv :=
    (lpReplicaCopySubsetEquivProfile G sites m P).trans
      (Equiv.cast (congrArg (Copy H) hP))
  let rightEquiv :=
    (lpReplicaCopyNotMemEquivCompl G sites m P).trans
      ((lpReplicaCopySubsetEquivProfile G sites m (Finset.univ \ P)).trans
        (Equiv.cast (congrArg (Copy H) hcompl)))
  let split : Copy H m ≃ Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) :=
    (Equiv.sumCompl (fun c : Copy H m => c ∈ P)).symm |>.trans
      (Equiv.sumCongr leftEquiv rightEquiv)
  let collide : Copy H a ⊕ Copy H (fun e =>
      b (lpReplicaCurrentEdgeReflect G sites e)) ≃
      Copy H (lpReplicaCollisionProfile G sites a b) :=
    (Equiv.sigmaSumDistrib
        (fun e : H.edgeFinset => Fin (a e))
        (fun e : H.edgeFinset =>
          Fin (b (lpReplicaCurrentEdgeReflect G sites e)))).symm |>.trans
      (lpReplicaCollisionCopyEquiv G sites a b)
  change (split.trans collide).symm
      (lpReplicaCollisionRightCopyEmbedding G sites a b d) = _
  rw [Equiv.symm_trans_apply]
  have hcollide : collide.symm
      (lpReplicaCollisionRightCopyEmbedding G sites a b d) =
        Sum.inr (lpReplicaReflectCopyEquiv G sites b d) := by
    apply collide.injective
    rw [collide.apply_symm_apply]
    rfl
  rw [hcollide]
  simp [split, rightEquiv, lpReplicaCopyNotMemEquivCompl]
  rw [← Equiv.cast_symm, Equiv.cast_apply]

set_option maxHeartbeats 800000 in


theorem lpReplicaOrbitCollisionSplitEquiv_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP c).1 = c.1 := by
  classical
  subst a
  by_cases hc : c ∈ P
  · simp [lpReplicaOrbitCollisionSplitEquiv, hc,
      lpReplicaCopySubsetEquivProfile, lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCollisionCopyEquiv, Sigma.map]
  · simp [lpReplicaOrbitCollisionSplitEquiv, hc,
      lpReplicaCopySubsetEquivProfile, lpReplicaCopySubsetSigmaEquiv,
      lpReplicaCopyNotMemEquivCompl, lpReplicaCollisionCopyEquiv, Sigma.map]
    apply lpReplicaCopy_cast_edge
    exact lpReplicaCollisionSplit_complProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P) P rfl


theorem lpReplicaOrbitCollisionSplitEquiv_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hP : profileFlux (lpReplicaCurrentGraph G sites) m P = a)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a
          (lpReplicaReflectedResidual G sites m a))
        (lpReplicaOrbitCollisionSplitEquiv G sites m a P hP c) =
      endsM (lpReplicaCurrentGraph G sites) m c := by
  unfold endsM
  rw [lpReplicaOrbitCollisionSplitEquiv_edge]


end
end StatMech.Ising
