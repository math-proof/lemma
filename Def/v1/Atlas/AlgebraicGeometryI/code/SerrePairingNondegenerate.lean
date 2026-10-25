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
import Structure.v1.Atlas.AlgebraicGeometryI.code.SerrePairingNondegenerate


noncomputable section

namespace SerrePairingNondegenerate

variable (k : Type*) [Field k]

attribute [instance] SerrePairingData.K_acg SerrePairingData.K_mod
  SerrePairingData.H0dual_acg SerrePairingData.H0dual_mod
  SerrePairingData.H0dual_fd

variable {k}

/-- Čech `H¹` of a Serre pairing data: the quotient `K / (V₁ + V₂)`. -/
def SerrePairingData.H1 (D : SerrePairingData k) : Type _ :=
  D.K ⧸ (D.V₁ ⊔ D.V₂)

end SerrePairingNondegenerate
end
