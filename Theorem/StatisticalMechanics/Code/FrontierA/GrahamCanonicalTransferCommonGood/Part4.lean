/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferCommonGood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCommonGood.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskOrbitCommonReference_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c ∈
        canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c ∧
      ∀ r ∈ canonicalMaskOrbitCommonReferenceFinset
          ends m j k l zero p c,
        canonicalMaskOrbitScore ends m k zero p
            (canonicalMaskOrbitCommonReference
              ends m j k l zero p hcommon c) ≤
          canonicalMaskOrbitScore ends m k zero p r :=
  Classical.choose_spec
    ((canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (hcommon c))

theorem canonicalMaskOrbitCommonReference_eq_of_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c =
      canonicalMaskOrbitCommonReference ends m j k l zero p hcommon d := by
  let rc := canonicalMaskOrbitCommonReference
    ends m j k l zero p hcommon c
  let rd := canonicalMaskOrbitCommonReference
    ends m j k l zero p hcommon d
  have hrc := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon c).1
  have hrd := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon d).1
  have hrcSpec := (mem_canonicalMaskOrbitCommonReferenceFinset_iff
    ends m j k l zero p c rc).mp hrc
  have hrdSpec := (mem_canonicalMaskOrbitCommonReferenceFinset_iff
    ends m j k l zero p d rd).mp hrd
  have hrdc : rd ∈ canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c := by
    rw [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
    refine ⟨hcd.trans hrdSpec.1, ?_⟩
    intro x hcx
    exact hrdSpec.2 x
      ((canonicalMaskTransferOrbit_symm
        ends m j k l zero p hcd).trans hcx)
  have hrcd : rc ∈ canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p d := by
    rw [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
    refine ⟨(canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcd).trans hrcSpec.1, ?_⟩
    intro x hdx
    exact hrcSpec.2 x (hcd.trans hdx)
  have hle := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon c).2 rd hrdc
  have hge := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon d).2 rc hrcd
  apply canonicalMaskOrbitScore_injective ends m j k l zero p
  exact le_antisymm hle hge

theorem canonicalMaskOrbitCommonReference_selector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
    IsCanonicalMaskOrbitSelector ends m j k l zero p
      (canonicalMaskOrbitCommonReference
        ends m j k l zero p hcommon) := by
  constructor
  · intro c
    exact (mem_canonicalMaskOrbitCommonReferenceFinset_iff
      ends m j k l zero p c
        (canonicalMaskOrbitCommonReference
          ends m j k l zero p hcommon c)).mp
            (canonicalMaskOrbitCommonReference_spec
              ends m j k l zero p hcommon c).1 |>.1
  · exact canonicalMaskOrbitCommonReference_eq_of_orbit
      ends m j k l zero p hcommon

theorem canonicalMaskOrbitCommonReference_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero
      (canonicalMaskOrbitCommonReference
        ends m j k l zero p hcommon c).1.1 c.1.1 := by
  have hspec := (mem_canonicalMaskOrbitCommonReferenceFinset_iff
    ends m j k l zero p c
      (canonicalMaskOrbitCommonReference
        ends m j k l zero p hcommon c)).mp
          (canonicalMaskOrbitCommonReference_spec
            ends m j k l zero p hcommon c).1
  exact hspec.2 c
    (canonicalMaskTransferOrbit_refl ends m j k l zero p c)


end StatMech.GrahamGHS.FourColor
