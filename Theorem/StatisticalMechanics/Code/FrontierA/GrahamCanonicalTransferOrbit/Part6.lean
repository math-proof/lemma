/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part6
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem leftMaskFiber_card_le_right_of_canonicalOrbitSelector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (rho : leftMaskFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p)
    (hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho)
    (hdisconnect : ∀ c,
      RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m (rho c).1.1 k zero)
          (canonicalOuterTransfer ends m (rho c).1.1 k zero)
          c.1.1) k zero) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  Fintype.card_le_of_injective
    (canonicalOrbitSelectorMaskFiberEmbedding
      ends m j k l zero hloop hjk hkl p rho hrho hdisconnect)
    (canonicalOrbitSelectorMaskFiberEmbedding
      ends m j k l zero hloop hjk hkl p rho hrho hdisconnect).injective


end StatMech.GrahamGHS.FourColor
