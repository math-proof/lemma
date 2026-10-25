/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskOrbitCommonReferenceFinset_eq_of_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c =
      canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p d := by
  ext r
  simp only [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
  constructor
  · rintro ⟨hcr, hgood⟩
    refine ⟨(canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcd).trans hcr, ?_⟩
    intro x hdx
    exact hgood x (hcd.trans hdx)
  · rintro ⟨hdr, hgood⟩
    refine ⟨hcd.trans hdr, ?_⟩
    intro x hcx
    exact hgood x ((canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcd).trans hcx)


end StatMech.GrahamGHS.FourColor
