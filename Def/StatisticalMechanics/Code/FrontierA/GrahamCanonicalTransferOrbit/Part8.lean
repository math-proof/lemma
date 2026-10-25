/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part7
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskOrbitDescentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hdescent : CanonicalMaskOrbitLocalDescent ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p :=
  canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p
    (canonicalMaskOrbitMinimumReference ends m j k l zero p)
    (canonicalMaskOrbitMinimumReference_selector ends m j k l zero p)
    (canonicalMaskOrbitMinimumReference_disconnects
      ends m j k l zero p hdescent)


end StatMech.GrahamGHS.FourColor
