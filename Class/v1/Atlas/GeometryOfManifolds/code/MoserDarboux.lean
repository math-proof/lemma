/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticStandardBasis
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticEvenDim
import Theorem.v1.Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux
set_option autoImplicit false

universe u_chart v_chart

open Module FiniteDimensional Finset
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Axiomatization of finite-dimensional behavior of the interior-product map: for a
nondegenerate $2$-form $\omega$, the map $X \mapsto \iota_X\omega$ is bijective, and the
interpolation $(1 - t)\omega_0 + t\omega_1$ of two nondegenerate closed forms remains
nondegenerate for $t \in [0, 1]$. -/
class HasFiniteDimContraction (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  contraction_surjective_of_injective :
    ∀ (ω : Ω 2), Function.Injective (fun X => inst.ι X ω) →
      Function.Surjective (fun X => inst.ι X ω)
  interpolated_contraction_injective :
    ∀ (ω₀ ω₁ : Ω 2),
      inst.d ω₀ = 0 → inst.d ω₁ = 0 →
      Function.Injective (fun X => inst.ι X ω₀) →
      Function.Injective (fun X => inst.ι X ω₁) →
      ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        Function.Injective (fun (X : VF) => inst.ι X ((1 - t) • ω₀ + t • ω₁))

