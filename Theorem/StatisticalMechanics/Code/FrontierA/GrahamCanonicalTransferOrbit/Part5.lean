/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part5
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskOrbitMinimumReference_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitMinimumReference ends m j k l zero p c ∈
        canonicalMaskTransferOrbitFinset ends m j k l zero p c ∧
      ∀ d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c,
        canonicalMaskOrbitScore ends m k zero p
            (canonicalMaskOrbitMinimumReference ends m j k l zero p c) ≤
          canonicalMaskOrbitScore ends m k zero p d :=
  Classical.choose_spec
    ((canonicalMaskTransferOrbitFinset ends m j k l zero p c).exists_min_image
      (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
      (canonicalMaskTransferOrbitFinset_nonempty
        ends m j k l zero p c))

theorem canonicalMaskOrbitMinimumReference_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferOrbit ends m j k l zero p c
      (canonicalMaskOrbitMinimumReference ends m j k l zero p c) := by
  rw [← mem_canonicalMaskTransferOrbitFinset_iff]
  exact (canonicalMaskOrbitMinimumReference_spec
    ends m j k l zero p c).1

theorem canonicalMaskOrbitMinimumReference_score_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitScore ends m k zero p
        (canonicalMaskOrbitMinimumReference ends m j k l zero p c) ≤
      canonicalMaskOrbitScore ends m k zero p d := by
  apply (canonicalMaskOrbitMinimumReference_spec
    ends m j k l zero p c).2 d
  rwa [mem_canonicalMaskTransferOrbitFinset_iff]

theorem canonicalMaskOrbitMinimumReference_size_le
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalTransferSize ends m k zero
        (canonicalMaskOrbitMinimumReference ends m j k l zero p c).1.1 ≤
      canonicalTransferSize ends m k zero d.1.1 := by
  have hscore := canonicalMaskOrbitMinimumReference_score_le
    ends m j k l zero p c d hcd
  rw [canonicalMaskOrbitScore, canonicalMaskOrbitScore,
    Prod.Lex.toLex_le_toLex] at hscore
  omega

theorem canonicalMaskOrbitMinimumReference_eq_of_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitMinimumReference ends m j k l zero p c =
      canonicalMaskOrbitMinimumReference ends m j k l zero p d := by
  let rc := canonicalMaskOrbitMinimumReference ends m j k l zero p c
  let rd := canonicalMaskOrbitMinimumReference ends m j k l zero p d
  have hcrd : CanonicalMaskTransferOrbit ends m j k l zero p c rd :=
    hcd.trans (canonicalMaskOrbitMinimumReference_mem
      ends m j k l zero p d)
  have hdrc : CanonicalMaskTransferOrbit ends m j k l zero p d rc :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p hcd).trans
      (canonicalMaskOrbitMinimumReference_mem ends m j k l zero p c)
  have hle := canonicalMaskOrbitMinimumReference_score_le
    ends m j k l zero p c rd hcrd
  have hge := canonicalMaskOrbitMinimumReference_score_le
    ends m j k l zero p d rc hdrc
  apply canonicalMaskOrbitScore_injective ends m j k l zero p
  exact le_antisymm hle hge

theorem canonicalMaskOrbitMinimumReference_selector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    IsCanonicalMaskOrbitSelector ends m j k l zero p
      (canonicalMaskOrbitMinimumReference ends m j k l zero p) := by
  constructor
  · exact canonicalMaskOrbitMinimumReference_mem ends m j k l zero p
  · exact canonicalMaskOrbitMinimumReference_eq_of_orbit
      ends m j k l zero p


theorem canonicalTransfers_valid_on_sameMask
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    let X := canonicalMiddleTransfer ends m r.1.1 k zero
    let Y := canonicalOuterTransfer ends m r.1.1 k zero
    X ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 ∧
      Y ⊆ colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 ∧
      sources ends X = {k, l} ∧ sources ends Y = ∅ := by
  have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
  have hprofile :
      fourColorMaskProfile m r.1.1 = fourColorMaskProfile m c.1.1 :=
    r.2.trans c.2.symm
  have hmid : middleMask m r.1.1 = middleMask m c.1.1 :=
    congrArg Prod.fst hprofile
  have hout : outerMask m r.1.1 = outerMask m c.1.1 :=
    congrArg Prod.snd hprofile
  have hX : canonicalMiddleTransfer ends m r.1.1 k zero ⊆
      colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 := by
    have hr : canonicalMiddleTransfer ends m r.1.1 k zero ⊆
        middleMask m r.1.1 := by
      simpa only [middleMask] using hv.1
    rw [hmid] at hr
    simpa only [middleMask] using hr
  have hY : canonicalOuterTransfer ends m r.1.1 k zero ⊆
      colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 := by
    have hr : canonicalOuterTransfer ends m r.1.1 k zero ⊆
        outerMask m r.1.1 := by
      simpa only [outerMask] using hv.2.1
    rw [hout] at hr
    simpa only [outerMask] using hr
  exact ⟨hX, hY, hv.2.2.1, hv.2.2.2⟩


end StatMech.GrahamGHS.FourColor
