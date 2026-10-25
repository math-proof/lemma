/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part26


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

attribute [instance] instFintypeRayClassGroup

instance instFiniteIdealNorm' (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOf_absNorm_eq n).to_subtype

instance instFinitePrimesNorm' (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} :=
  Finite.of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

instance instFiniteIdealNorm_rl (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOf_absNorm_eq n).to_subtype

instance instFinitePrimesNorm_rl (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {𝔭 : Prime' K // Ideal.absNorm 𝔭.asIdeal = n} :=
  Finite.of_injective
    (fun ⟨𝔭, h⟩ => (⟨𝔭.asIdeal, h⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    (fun ⟨a, _⟩ ⟨b, _⟩ h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h))

end RayClassField
end
