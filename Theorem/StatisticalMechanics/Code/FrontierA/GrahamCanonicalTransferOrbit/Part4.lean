/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part4
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem mem_canonicalMaskTransferOrbitFinset_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c ↔
      CanonicalMaskTransferOrbit ends m j k l zero p c d := by
  classical
  simp [canonicalMaskTransferOrbitFinset]

theorem canonicalMaskTransferOrbitFinset_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskTransferOrbitFinset ends m j k l zero p c).Nonempty := by
  refine ⟨c, ?_⟩
  rw [mem_canonicalMaskTransferOrbitFinset_iff]
  exact canonicalMaskTransferOrbit_refl ends m j k l zero p c


end StatMech.GrahamGHS.FourColor
