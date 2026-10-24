/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FractionalIdeals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open nonZeroDivisors

noncomputable abbrev principalFractionalIdeal (x : K) : FractionalIdeal A⁰ K :=
  FractionalIdeal.spanSingleton A⁰ x

end PrincipalFractionalIdeals

section PrincipalFractionalIdealProps

variable (A : Type*) [CommRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

def IsInvertible (I : FractionalIdeal A⁰ K) : Prop :=
  ∃ J : FractionalIdeal A⁰ K, I * J = 1

noncomputable abbrev IdealGroup : Type _ := (FractionalIdeal A⁰ K)ˣ

instance IdealGroup.commGroup : CommGroup (IdealGroup A K) := inferInstance

noncomputable abbrev IdealClassGroup : Type _ := ClassGroup A

noncomputable instance IdealClassGroup.commGroup : CommGroup (IdealClassGroup A) := inferInstance

noncomputable abbrev PicardGroup : Type _ := IdealClassGroup A

noncomputable def IdealClassGroup.mk (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :
    (FractionalIdeal A⁰ K)ˣ →* IdealClassGroup A :=
  ClassGroup.mk
