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


noncomputable section

namespace SerrePairingNondegenerate

variable (k : Type*) [Field k]

/-- Data for a Serre pairing: a Čech-style two-cover `V₁, V₂ ⊆ K`, a finite-dimensional
"dual sections" space `H0dual`, and a residue pairing that vanishes on `V₁ + V₂`
and is right-separating. -/
structure SerrePairingData where
  K : Type*
  [K_acg : AddCommGroup K]
  [K_mod : Module k K]
  V₁ : Submodule k K
  V₂ : Submodule k K
  H0dual : Type*
  [H0dual_acg : AddCommGroup H0dual]
  [H0dual_mod : Module k H0dual]
  [H0dual_fd : FiniteDimensional k H0dual]
  residuePairing : K →ₗ[k] H0dual →ₗ[k] k
  residue_vanishes_on_image : ∀ (ω : H0dual) (f : K),
    f ∈ V₁ ⊔ V₂ → (residuePairing f) ω = 0
  residue_separating : ∀ (ω : H0dual),
    (∀ (f : K), (residuePairing f) ω = 0) → ω = 0

/-- Perfect Serre pairing data: a `SerrePairingData` with the additional
left-separating axiom — if the pairing vanishes on all `ω`, then `f ∈ V₁ + V₂`. -/
structure PerfectSerrePairingData extends SerrePairingData k where
  residue_separating_left : ∀ (f : K),
    (∀ (ω : H0dual), (residuePairing f) ω = 0) → f ∈ V₁ ⊔ V₂

end SerrePairingNondegenerate
end
