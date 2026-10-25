/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication


namespace IdealEquivalence

open ComplexLattice Pointwise

noncomputable section

/-- Two proper ideals `L₁`, `L₂` of an order `𝒪 ⊆ ℂ` are equivalent if they are
equivalent as complex lattices in the sense of `ComplexLattice.IsEquivalent`. -/
def IsEquivalent (𝒪 : Subring ℂ) (L₁ L₂ : ComplexLattice.ProperIdeal 𝒪) : Prop :=
  ComplexLattice.IsEquivalent 𝒪 L₁.val L₂.val

end
end IdealEquivalence
