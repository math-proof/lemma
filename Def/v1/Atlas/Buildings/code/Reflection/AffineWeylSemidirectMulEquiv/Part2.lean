/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct
import Abbrev.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv.Part2
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

/-- Map sending $g ∈ W_a$ to the pair $(g\cdot 0,\ \mathrm{linearPart}(g))$ in the
semidirect product. -/
def toSemidirect (g : ↥d.affineWeylSubgroup) : d.SemiType :=
  ⟨Multiplicative.ofAdd ⟨(g : E ≃ᵃⁱ[ℝ] E) 0, d.translationPart_mem g g.prop⟩,
   ⟨linearPartHom (g : E ≃ᵃⁱ[ℝ] E), d.linearPart_mem g g.prop⟩⟩

end AffineWeylSemidirectData
end
