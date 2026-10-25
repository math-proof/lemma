/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part26
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawPreferredRightBase_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d ∈
      canonicalRawCommonClosure ends m j k l zero p := by
  classical
  unfold canonicalStableRawPreferredRightBase
  split
  next hself =>
    exact (canonicalStableRawPreferredSelfPreimage
      ends m j k l zero hloop hjk hkl hk0 p d hself).2
  next => exact canonicalStableRawRightBase_mem ends m j k l zero p d

theorem canonicalStableRawPreferredRightBase_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    CanonicalRawGateRelated ends m j k l zero p
      (canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d) d.1 := by
  classical
  unfold canonicalStableRawPreferredRightBase
  split
  next hself =>
    let preferred := canonicalStableRawPreferredSelfPreimage
      ends m j k l zero hloop hjk hkl hk0 p d hself
    have hpreferred := (canonicalStableRawPreferredSelfPreimage_spec
      ends m j k l zero hloop hjk hkl hk0 p d hself).1
    have hpreferredSelf : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p preferred = d.1 := by
      simpa only [canonicalStableRawSelfPreimageFinset,
        Finset.mem_filter, Finset.mem_univ, true_and] using hpreferred
    have hr := canonicalStableRawSelfBase_related ends m j k l zero
      hloop hjk hkl hk0 p preferred
    simpa only [hpreferredSelf, preferred] using hr
  next =>
    exact canonicalStableRawRightBase_related ends m j k l zero p d

theorem canonicalStableRawPreferredRightBase_self_eq_of_exists
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c = d.1) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p d⟩ = d.1 := by
  classical
  let c := Classical.choose hself
  have hpreferred :=
    (canonicalStableRawPreferredSelfPreimage_spec
      ends m j k l zero hloop hjk hkl hk0 p d hself).1
  have hbase : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p
        (canonicalStableRawPreferredSelfPreimage ends m j k l zero
          hloop hjk hkl hk0 p d hself) = d.1 := by
    simpa only [canonicalStableRawSelfPreimageFinset,
      Finset.mem_filter, Finset.mem_univ, true_and] using hpreferred
  change canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p d⟩ = d.1
  simpa only [canonicalStableRawPreferredRightBase, dif_pos hself] using hbase


theorem canonicalStableRawPreferredRightBase_rank_lt_of_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hself : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p c = d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    canonicalStableRawSourceRank ends m j k l zero p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p d⟩ <
      canonicalStableRawSourceRank ends m j k l zero p c := by
  classical
  let hExists : ∃ b : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p b = d.1 := ⟨c, hself⟩
  let preferred := canonicalStableRawPreferredSelfPreimage
    ends m j k l zero hloop hjk hkl hk0 p d hExists
  have hcMem : c ∈ canonicalStableRawSelfPreimageFinset
      ends m j k l zero hloop hjk hkl hk0 p d := by
    simp only [canonicalStableRawSelfPreimageFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hself
  have hle : canonicalStableRawSourceRank ends m j k l zero p preferred ≤
      canonicalStableRawSourceRank ends m j k l zero p c :=
    (canonicalStableRawPreferredSelfPreimage_spec
      ends m j k l zero hloop hjk hkl hk0 p d hExists).2 c hcMem
  have hpreferred :
      (⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p d⟩ :
        ↑(canonicalRawCommonClosure ends m j k l zero p)) = preferred := by
    apply Subtype.ext
    simp only [canonicalStableRawPreferredRightBase, dif_pos hExists,
      preferred]
  have hpreferredNe : preferred ≠ c := by
    intro heq
    apply hne
    calc
      c.1 = preferred.1 := congrArg Subtype.val heq.symm
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d := (congrArg Subtype.val hpreferred).symm
  have hrankNe : canonicalStableRawSourceRank ends m j k l zero p preferred ≠
      canonicalStableRawSourceRank ends m j k l zero p c := by
    intro heq
    apply hpreferredNe
    apply (Fintype.equivFin
      (↑(canonicalRawCommonClosure ends m j k l zero p))).injective
    apply Fin.ext
    exact heq
  rw [hpreferred]
  omega


theorem exists_canonicalRawGateRelated_ne_self_of_exceptionalSelfToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p c = d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    ∃ e : leftSourceMaskFiber ends m j k l zero p,
      CanonicalRawGateRelated ends m j k l zero p c.1 e ∧
        e ≠ canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c := by
  classical
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p d,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p d⟩
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  have hcb : c ≠ b := by
    intro h
    exact hne (congrArg (fun x => x.1) h)
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let r := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  have har : a ≠ r := by
    intro h
    apply hcb
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x => x.1.1) h
  have hbself : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p b = d.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p d ⟨c, hself⟩
  let qa := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  let qr := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p b.1 hb
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  have heqa : (e qa).1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p c := by
    rfl
  have heqr : (e qr).1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p b := by
    rfl
  have heq : qa = qr := by
    apply e.injective
    apply Subtype.ext
    exact heqa.trans (hself.trans (hbself.symm.trans heqr.symm))
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p a a
          (canonicalTransferWorks_self hloop hjk hkl hk0 a)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1 := by
    exact congrArg (fun q => q.1.1) heq
  obtain ⟨qalt, hqalt, hqaltne⟩ :=
    exists_canonicalMaskRightImage_ne_self_of_selfImage_collision
      ends m j k l zero hloop hjk hkl hk0 p a r har himage
  let raw := (e qalt).1
  have hrawRight : RowsDisconnect ends m (middleSwap m raw.1) k zero :=
    (e qalt).2
  refine ⟨raw, ⟨hc, hrawRight, ?_⟩, ?_⟩
  · have hback : e.symm ⟨raw, hrawRight⟩ = qalt := by
      exact e.symm_apply_apply qalt
    rw [hback]
    exact hqalt
  · intro hraw
    apply hqaltne
    apply e.injective
    apply Subtype.ext
    exact hraw


end StatMech.GrahamGHS.FourColor
