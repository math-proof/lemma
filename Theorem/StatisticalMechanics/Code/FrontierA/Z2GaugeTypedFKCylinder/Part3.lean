/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part3
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem belowCut_eq_sheet_union_complement
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalBelowSpin (a := a) (b := b) k) =
      cubicalXYSheet (a := a) (b := b) k ∪
        cubicalLowerComplementSurface (a := a) (b := b) k := by
  have hsub := cubicalXYSheet_subset_belowCut
    (a := a) (b := b) k hk
  ext p
  simp only [cubicalLowerComplementSurface, Finset.mem_union,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalXYSheet k
    · exact Or.inl hD
    · exact Or.inr ⟨hp, hD⟩
  · rintro (hp | ⟨hp, _⟩)
    · exact hsub hp
    · exact hp

theorem belowCut_eq_sheet_symmDiff_complement
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    multibondCut (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalBelowSpin (a := a) (b := b) k) =
      cubicalXYSheet (a := a) (b := b) k ∆
        cubicalLowerComplementSurface (a := a) (b := b) k := by
  have hsub := cubicalXYSheet_subset_belowCut
    (a := a) (b := b) k hk
  ext p
  simp only [cubicalLowerComplementSurface, Finset.mem_symmDiff,
    Finset.mem_sdiff]
  constructor
  · intro hp
    by_cases hD : p ∈ cubicalXYSheet k
    · exact Or.inl ⟨hD, fun h => h.2 hD⟩
    · exact Or.inr ⟨⟨hp, hD⟩, hD⟩
  · rintro (⟨hp, _⟩ | ⟨⟨hp, _⟩, _⟩)
    · exact hsub hp
    · exact hp

end
end StatMech.FrontierA
