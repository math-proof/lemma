/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part3
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem internalCentralCut_eq_sheet_union_complement
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) =
      cubicalInternalCentralSheet N m hNm ∪
        cubicalInternalCentralComplement N m hNm := by
  have hsub := cubicalInternalCentralSheet_subset_cut N m hN hNm
  ext p
  simp only [cubicalInternalCentralComplement, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalInternalCentralSheet N m hNm
    · exact Or.inl hD
    · exact Or.inr ⟨hp, hD⟩
  · rintro (hp | ⟨hp, _⟩)
    · exact hsub hp
    · exact hp

theorem internalCentralCut_eq_sheet_symmDiff_complement
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    multibondCut cubicalDualEnds (cubicalInternalCentralBlockSpin N m) =
      cubicalInternalCentralSheet N m hNm ∆
        cubicalInternalCentralComplement N m hNm := by
  have hsub := cubicalInternalCentralSheet_subset_cut N m hN hNm
  ext p
  simp only [cubicalInternalCentralComplement, Finset.mem_symmDiff,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalInternalCentralSheet N m hNm
    · exact Or.inl ⟨hD, fun h => h.2 hD⟩
    · exact Or.inr ⟨⟨hp, hD⟩, hD⟩
  · rintro (⟨hp, _⟩ | ⟨⟨hp, _⟩, _⟩)
    · exact hsub hp
    · exact hp

end
end StatMech.FrontierA
