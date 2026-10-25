/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem nonempty_maskFiberEmbeddings_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    Nonempty (MaskFiberEmbeddings ends m j k l zero) ↔
      forall p : Finset I × Finset I,
        Fintype.card (leftMaskFiber ends m j k l zero p) <=
          Fintype.card (rightMaskFiber ends m j k l zero p) := by
  classical
  constructor
  · rintro ⟨f⟩ p
    exact Fintype.card_le_of_injective (f p) (f p).injective
  · intro h
    exact ⟨fun p => Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (h p))⟩


theorem GrahamFiberMinor_of_maskFiberEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskwise
  intro p
  exact Fintype.card_le_of_injective (f p) (f p).injective


end StatMech.GrahamGHS.FourColor
