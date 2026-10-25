/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Def.v1.Atlas.EllipticCurves.code.IdealEquivalence


namespace IdealEquivalence

open ComplexLattice Pointwise

noncomputable section

/-- Reflexivity of ideal equivalence: every proper ideal is equivalent to itself. -/
theorem IsEquivalent.refl (𝒪 : Subring ℂ) (L : ComplexLattice.ProperIdeal 𝒪) :
    IsEquivalent 𝒪 L L :=
  ComplexLattice.IsEquivalent.refl 𝒪 L.val

/-- Transitivity of ideal equivalence: `L₁ ~ L₂` and `L₂ ~ L₃` imply `L₁ ~ L₃`. -/
theorem IsEquivalent.trans {𝒪 : Subring ℂ} {L₁ L₂ L₃ : ComplexLattice.ProperIdeal 𝒪}
    (h₁₂ : IsEquivalent 𝒪 L₁ L₂) (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
    IsEquivalent 𝒪 L₁ L₃ :=
  ComplexLattice.IsEquivalent.trans h₁₂ h₂₃

/-- `IsEquivalent 𝒪` is an equivalence relation on proper ideals of `𝒪`. -/
theorem isEquivalent_equivalence (𝒪 : Subring ℂ) :
    Equivalence (IsEquivalent 𝒪) :=
  ⟨IsEquivalent.refl 𝒪, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

end
end IdealEquivalence
