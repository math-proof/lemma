/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
import Structure.v1.Atlas.TensorCategories.code.Twists
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section IsBialgebraTwistDef

variable (R : Type u) [CommSemiring R]

variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- The twisted associator built from `J` and `J⁻¹` using the four maps `embedRight`,
`idTensorComul`, `comulTensorId`, `embedLeft`. -/
noncomputable def BialgebraTwist.twistedAssociator
    (J : (H ⊗[R] H)ˣ) : H ⊗[R] (H ⊗[R] H) :=
  BialgebraTwist.embedRight R H (↑J⁻¹ : H ⊗[R] H) *
  BialgebraTwist.idTensorComul R H (↑J⁻¹ : H ⊗[R] H) *
  BialgebraTwist.comulTensorId R H (↑J : H ⊗[R] H) *
  BialgebraTwist.embedLeft R H (↑J : H ⊗[R] H)

/-- Predicate characterizing when `J ∈ (H ⊗ H)ˣ` is a bialgebra twist: counit
normalization and trivial twisted associator. -/
def IsBialgebraTwist (J : (H ⊗[R] H)ˣ) : Prop :=

  BialgebraTwist.counitTensorId R H J.val = 1 ∧
  BialgebraTwist.idTensorCounit R H J.val = 1 ∧

  BialgebraTwist.twistedAssociator R H J = 1

end IsBialgebraTwistDef


namespace BialgebraTwist

variable {R : Type u} [CommSemiring R]

variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Twisted comultiplication of `H` along a bialgebra twist `T`: `Δ_T(x) = J⁻¹ Δ(x) J`. -/
noncomputable def twistedComul (T : BialgebraTwist R H) (x : H) : H ⊗[R] H :=
  ↑T.J⁻¹ * Bialgebra.comulAlgHom R H x * ↑T.J

end BialgebraTwist


section GaugeEquiv

variable {R : Type u} [CommSemiring R]

variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Gauge equivalence of twists: `J₁ ∼ J₂` iff there is a unit `v ∈ Hˣ` with
`J₂ = Δ(v) · J₁ · (v⁻¹ ⊗ v⁻¹)`. -/
def GaugeEquiv (J₁ J₂ : (H ⊗[R] H)ˣ) : Prop :=
  ∃ v : Hˣ, (J₂ : H ⊗[R] H) = Bialgebra.comulAlgHom R H (v : H) *
    (J₁ : H ⊗[R] H) * ((↑v⁻¹ : H) ⊗ₜ[R] (↑v⁻¹ : H))

end GaugeEquiv
