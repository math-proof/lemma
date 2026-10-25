/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerrePairingNondegenerate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Instance.v1.Atlas.AlgebraicGeometryI.code.SerrePairingNondegenerate


noncomputable section

namespace SerrePairingNondegenerate

variable (k : Type*) [Field k]

attribute [instance] SerrePairingData.K_acg SerrePairingData.K_mod
  SerrePairingData.H0dual_acg SerrePairingData.H0dual_mod
  SerrePairingData.H0dual_fd

variable {k}

/-- The Serre pairing `H¹ × H0dual → k` obtained by descending the residue
pairing through the quotient `K → K/(V₁ + V₂)`. -/
def SerrePairingData.serrePairing (D : SerrePairingData k) :
    D.H1 →ₗ[k] D.H0dual →ₗ[k] k :=
  Submodule.liftQ (D.V₁ ⊔ D.V₂) D.residuePairing (by
    intro f hf
    ext ω
    simp only [LinearMap.zero_apply]
    exact D.residue_vanishes_on_image ω f hf)

end SerrePairingNondegenerate
end
