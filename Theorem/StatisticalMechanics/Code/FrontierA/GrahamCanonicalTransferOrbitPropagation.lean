/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitPropagation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitPropagation
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskOrbitMinimumReference_disconnects_of_adjacentStrictDescent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hlocal : CanonicalMaskAdjacentStrictDescent
      ends m j k l zero p)
    (d : leftMaskFiber ends m j k l zero p) :
    RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        (canonicalOuterTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        d.1.1) k zero := by
  let r := canonicalMaskOrbitMinimumReference ends m j k l zero p d
  have hdr : CanonicalMaskTransferOrbit ends m j k l zero p d r :=
    canonicalMaskOrbitMinimumReference_mem ends m j k l zero p d
  have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
    canonicalMaskTransferOrbit_symm ends m j k l zero p hdr
  have propagate : ∀ e : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r e ->
        RowsDisconnect ends m
          (balancedSwap m
            (canonicalMiddleTransfer ends m r.1.1 k zero)
            (canonicalOuterTransfer ends m r.1.1 k zero)
            e.1.1) k zero := by
    intro e hre
    induction hre with
    | refl =>
        exact canonicalBalancedSwap_disconnects
          hloop hjk hkl hk0 r.1.2
    | @tail c e hrc hce ih =>
        by_contra hbad
        have hproper := hlocal r c e hce ih hbad
        have hlt : canonicalTransferSize ends m k zero e.1.1 <
            canonicalTransferSize ends m k zero r.1.1 := by
          rw [canonicalTransferSize_eq_card_union hloop hjk hkl e.1.2,
            canonicalTransferSize_eq_card_union hloop hjk hkl r.1.2]
          exact Finset.card_lt_card hproper
        have hde : CanonicalMaskTransferOrbit ends m j k l zero p d e :=
          hdr.trans (hrc.tail hce)
        have hle : canonicalTransferSize ends m k zero r.1.1 ≤
            canonicalTransferSize ends m k zero e.1.1 := by
          simpa only [r] using canonicalMaskOrbitMinimumReference_size_le
            ends m j k l zero p d e hde
        exact (not_lt_of_ge hle) hlt
  exact propagate d hrd


end StatMech.GrahamGHS.FourColor
