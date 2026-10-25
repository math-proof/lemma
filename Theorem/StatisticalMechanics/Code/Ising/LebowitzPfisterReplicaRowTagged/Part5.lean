/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

section CollisionTag

variable [Fintype I] [DecidableEq I]

theorem lpReplicaCollisionRowGate
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (A B : Finset (LPReplicaCurrentVertex V))
    (hSa : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) a) Sa = A)
    (hSa' : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) a)
      (Finset.univ \ Sa) = ∅)
    (hda : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) a) Finset.univ
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hSb : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) b) Sb = B)
    (hSb' : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) b)
      (Finset.univ \ Sb) = ∅)
    (hdb : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) b) Finset.univ
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites
      (lpReplicaCollisionProfile G sites a b) A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCollisionRowTag G sites a b Sa Sb) := by
  have hdisc0 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [lpReplicaCollision_rowCopies_false]
    exact fun h => hda
      ((randomCurrent_connK_map_embedding
        (endsM (lpReplicaCurrentGraph G sites) a)
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCollisionLeftCopyEmbedding G sites a b)
        (lpReplicaCollisionLeftCopyEmbedding_ends G sites a b)
        Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).1 h)
  have hdisc1 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b))
      (lpReplicaRowCopies G sites
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRowTag G sites a b Sa Sb) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [lpReplicaCollision_rowCopies_true]
    intro h
    let mappedEnds := fun c : Copy (lpReplicaCurrentGraph G sites) b =>
      Sym2.map lpReplicaCurrentReflect
        (endsM (lpReplicaCurrentGraph G sites) b c)
    have hmapped : RandomCurrent.connK mappedEnds Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 :=
      (randomCurrent_connK_map_embedding mappedEnds
        (endsM (lpReplicaCurrentGraph G sites)
          (lpReplicaCollisionProfile G sites a b))
        (lpReplicaCollisionRightCopyEmbedding G sites a b)
        (lpReplicaCollisionRightCopyEmbedding_ends G sites a b)
        Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).1 h
    have hreflected : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => b (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites b Finset.univ)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 :=
      (randomCurrent_connK_map_embedding mappedEnds
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => b (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopyEquiv G sites b).toEmbedding
        (lpReplicaReflectCopyEquiv_ends G sites b)
        Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).2 hmapped
    have horiginal : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) b) Finset.univ
        lpReplicaCurrentGhost1 lpReplicaCurrentGhost0 := by
      have htransport :=
        (lpReplicaReflectCopies_connK G sites b Finset.univ
          lpReplicaCurrentGhost1 lpReplicaCurrentGhost0).1
      apply htransport
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hreflected
    exact hdb (RandomCurrent.connK_symm _ _ horiginal)
  unfold LPReplicaRowGate
  refine ⟨?_, ?_, hdisc0, ?_, ?_, hdisc1⟩
  · rw [lpReplicaCollision_leftSources]
    simpa using hSa
  · rw [lpReplicaCollision_leftSources]
    simpa using hSa'
  · rw [lpReplicaCollision_rightSources]
    simpa using congrArg
      (Finset.map lpReplicaCurrentReflect.toEmbedding) hSb
  · rw [lpReplicaCollision_rightSources]
    simpa using congrArg
      (Finset.map lpReplicaCurrentReflect.toEmbedding) hSb'

end CollisionTag

section Reflection

variable [Fintype I] [DecidableEq I]

theorem lpReplicaRowGate_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    LPReplicaRowGate G sites
      (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
      (A.map lpReplicaCurrentReflect.toEmbedding)
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaReflectTag G sites m tag) := by
  unfold LPReplicaRowGate at hgate ⊢
  have hdisc : ∀ row,
      (¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag row)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ->
      ¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaRowCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro row hrow hconn
    have hreflected : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaRowCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost1)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost0) := by
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hconn
    have horiginal :=
      (lpReplicaRowConn_reflectTag G sites m tag row
        lpReplicaCurrentGhost1 lpReplicaCurrentGhost0).1 hreflected
    exact hrow (RandomCurrent.connK_symm _ _ horiginal)
  refine ⟨?_, ?_, hdisc false hgate.2.2.1, ?_, ?_,
    hdisc true hgate.2.2.2.2.2⟩
  · rw [lpReplicaCurrentSources_reflectTag, hgate.1]
  · rw [lpReplicaCurrentSources_reflectTag, hgate.2.1]
    simp
  · rw [lpReplicaCurrentSources_reflectTag, hgate.2.2.2.1]
  · rw [lpReplicaCurrentSources_reflectTag, hgate.2.2.2.2.1]
    simp

end Reflection

theorem lpReplicaRowGate_rowSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m A B tag) :
    RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag false) = A ∧
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag true) = B := by
  unfold LPReplicaRowGate at hgate
  constructor
  · rw [lpReplicaRowSources_eq_currentSources, hgate.1, hgate.2.1]
    simp
  · rw [lpReplicaRowSources_eq_currentSources, hgate.2.2.2.1,
      hgate.2.2.2.2.1]
    simp

theorem lpReplicaRowGate_toggle
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hgate : LPReplicaRowGate G sites m A B tag)
    (hsecond : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = true)) = ∅)
    (hdisc0 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let X := RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = false))
    LPReplicaRowGate G sites m (A ∆ X) (B ∆ X)
      (lpReplicaToggleRows G sites m P tag) := by
  dsimp only
  unfold LPReplicaRowGate at hgate ⊢
  refine ⟨?_, ?_, hdisc0, ?_, ?_, hdisc1⟩
  · rw [lpReplicaCurrentSources_toggle, hgate.1]
  · rw [lpReplicaCurrentSources_toggle, hgate.2.1, hsecond]
    simp
  · rw [lpReplicaCurrentSources_toggle, hgate.2.2.2.1]
  · rw [lpReplicaCurrentSources_toggle, hgate.2.2.2.2.1, hsecond]
    simp

theorem lpReplicaRowGate_toggle_offdiag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hgate : LPReplicaRowGate G sites m (Si ∆ Sj ∆ T) ∅ tag)
    (hfirst : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = false)) = Sj ∆ T)
    (hsecond : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (P.filter (fun c => (tag c).2 = true)) = ∅)
    (hdisc0 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
    (hdisc1 : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P tag) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaRowGate G sites m Si (Sj ∆ T)
      (lpReplicaToggleRows G sites m P tag) := by
  have h := lpReplicaRowGate_toggle G sites m (Si ∆ Sj ∆ T) ∅
    tag P hgate hsecond hdisc0 hdisc1
  dsimp only at h
  rw [hfirst] at h
  have hsource : (Si ∆ Sj ∆ T) ∆ (Sj ∆ T) = Si := by
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  rw [hsource] at h
  have hB : (∅ : Finset (LPReplicaCurrentVertex V)) ∆ (Sj ∆ T) =
      Sj ∆ T := by
    ext x
    simp [Finset.mem_symmDiff]
  rw [hB] at h
  exact h

end
end StatMech.Ising
