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
import Abbrev.v1.Atlas.NumberTheoryI.code.RayClassFields.Part3


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

attribute [instance] instFintypeRayClassGroup

noncomputable def partialDedekindZeta (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : ℂ → ℂ := fun s =>
  ∏' (𝔭 : S), (1 - (Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℂ) ^ (-s))⁻¹


def HasMeromorphicContinuationWithPoleOrder (f : ℂ → ℂ) (m : ℤ) : Prop :=
  MeromorphicAt f 1 ∧ meromorphicOrderAt f 1 = ↑(-m)

def HasPolarDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) (ρ : ℚ) : Prop :=
  ∃ (n : ℕ+) (m : ℤ),
    HasMeromorphicContinuationWithPoleOrder (partialDedekindZeta K S ^ (n : ℕ)) m ∧
    (ρ : ℚ) = (m : ℚ) / (n : ℚ)

def HasDirichletDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) (ρ : ℚ) : Prop :=
  Filter.Tendsto (fun s : ℝ =>
    (∑' (𝔭 : S), ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
    Real.log (1 / (s - 1)))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds (ρ : ℝ))

def HasNaturalDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) (ρ : ℚ) : Prop :=
  Filter.Tendsto (fun x : ℝ =>
    (Set.ncard {𝔭 : Prime' K | 𝔭 ∈ S ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} : ℝ) /
    (Set.ncard {𝔭 : Prime' K | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x} : ℝ))
    Filter.atTop (nhds (ρ : ℝ))

end RayClassField
end
