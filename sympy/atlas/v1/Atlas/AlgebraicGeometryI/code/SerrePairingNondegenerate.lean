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

attribute [instance] SerrePairingData.K_acg SerrePairingData.K_mod
  SerrePairingData.H0dual_acg SerrePairingData.H0dual_mod
  SerrePairingData.H0dual_fd

variable {k}

/-- Čech `H¹` of a Serre pairing data: the quotient `K / (V₁ + V₂)`. -/
def SerrePairingData.H1 (D : SerrePairingData k) : Type _ :=
  D.K ⧸ (D.V₁ ⊔ D.V₂)

/-- `H¹` of a Serre pairing data is an additive commutative group. -/
instance (D : SerrePairingData k) : AddCommGroup D.H1 :=
  inferInstanceAs (AddCommGroup (D.K ⧸ (D.V₁ ⊔ D.V₂)))

/-- `H¹` is a `k`-module. -/
instance (D : SerrePairingData k) : Module k D.H1 :=
  inferInstanceAs (Module k (D.K ⧸ (D.V₁ ⊔ D.V₂)))

/-- The Serre pairing `H¹ × H0dual → k` obtained by descending the residue
pairing through the quotient `K → K/(V₁ + V₂)`. -/
def SerrePairingData.serrePairing (D : SerrePairingData k) :
    D.H1 →ₗ[k] D.H0dual →ₗ[k] k :=
  Submodule.liftQ (D.V₁ ⊔ D.V₂) D.residuePairing (by
    intro f hf
    ext ω
    simp only [LinearMap.zero_apply]
    exact D.residue_vanishes_on_image ω f hf)
