/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Structure.v1.Atlas.TensorCategories.code.Proposition_1_36_4
open scoped TensorProduct
open CategoryTheory

universe u


section Prop1364GaugeEquiv

variable {R : Type u} [CommSemiring R]

variable {H : Type u} [Semiring H] [Bialgebra R H]

/-- Gauge equivalence on bialgebra twists: `J₁ ~ J₂` iff there is a unit `v ∈ Hˣ` with
`J₂ = Δ(v) · J₁ · (v⁻¹ ⊗ v⁻¹)`. -/
def Prop1364.GaugeEquiv (J₁ J₂ : (H ⊗[R] H)ˣ) : Prop :=
  ∃ v : Hˣ, (J₂ : H ⊗[R] H) = Bialgebra.comulAlgHom R H (v : H) *
    (J₁ : H ⊗[R] H) * ((↑v⁻¹ : H) ⊗ₜ[R] (↑v⁻¹ : H))

end Prop1364GaugeEquiv
