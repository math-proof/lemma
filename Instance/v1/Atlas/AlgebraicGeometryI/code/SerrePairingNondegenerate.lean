/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerrePairingNondegenerate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Def.v1.Atlas.AlgebraicGeometryI.code.SerrePairingNondegenerate

@[expose] public section

noncomputable section

namespace SerrePairingNondegenerate

variable (k : Type*) [Field k]

attribute [instance] SerrePairingData.K_acg SerrePairingData.K_mod
  SerrePairingData.H0dual_acg SerrePairingData.H0dual_mod
  SerrePairingData.H0dual_fd

variable {k}

/-- `H¹` of a Serre pairing data is an additive commutative group. -/
instance (D : SerrePairingData k) : AddCommGroup D.H1 :=
  inferInstanceAs (AddCommGroup (D.K ⧸ (D.V₁ ⊔ D.V₂)))

/-- `H¹` is a `k`-module. -/
instance (D : SerrePairingData k) : Module k D.H1 :=
  inferInstanceAs (Module k (D.K ⧸ (D.V₁ ⊔ D.V₂)))

end SerrePairingNondegenerate
end
