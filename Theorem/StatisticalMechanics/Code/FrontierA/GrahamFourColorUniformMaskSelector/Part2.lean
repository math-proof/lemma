/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


theorem exists_minimal_leftMaskCandidate
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι)
    (h : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c) :
    ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c ∧
        ∀ d : ↑m -> Fin 4,
          IsLeftMaskCandidate ends m j k l zero p d ->
            canonicalTransferSize ends m k zero c <=
              canonicalTransferSize ends m k zero d := by
  let S : Finset (↑m -> Fin 4) :=
    Finset.univ.filter (IsLeftMaskCandidate ends m j k l zero p)
  obtain ⟨c, hc⟩ := h
  have hcS : c ∈ S := by simp [S, hc]
  obtain ⟨r, hrS, hrmin⟩ := S.exists_min_image
    (canonicalTransferSize ends m k zero) ⟨c, hcS⟩
  have hr : IsLeftMaskCandidate ends m j k l zero p r := by
    simpa [S] using hrS
  refine ⟨r, hr, ?_⟩
  intro d hd
  apply hrmin d
  simp [S, hd]


end StatMech.GrahamGHS.FourColor
