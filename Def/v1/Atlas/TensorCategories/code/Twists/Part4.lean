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
import Abbrev.v1.Atlas.TensorCategories.code.Twists
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


section QuasiHopfTwist

open scoped TensorProduct

universe v

variable {R : Type u} [CommSemiring R]

variable {H : Type v} [Semiring H] [Algebra R H]

variable [qh : QuasiHopfAlgebra R H]

/-- Twisted `α`-element of a quasi-Hopf algebra under a twist `tw`. -/
noncomputable def QuasiBialgebraTwist.twistedAlpha
    (tw : QuasiBialgebraTwist R H) : H :=
  QuasiBialgebra.sAlphaMap R H qh.S.toLinearMap qh.α_elem (tw.J : H ⊗[R] H)

/-- Twisted `β`-element of a quasi-Hopf algebra under a twist `tw`. -/
noncomputable def QuasiBialgebraTwist.twistedBeta
    (tw : QuasiBialgebraTwist R H) : H :=
  QuasiBialgebra.betaSMap R H qh.S.toLinearMap qh.β_elem (↑tw.J⁻¹ : H ⊗[R] H)

/-- New quasi-Hopf algebra structure on `H` obtained by twisting an existing one along
a twist `tw`. -/

end QuasiHopfTwist


section Thm_1_35_6

open TensorCategories CategoryTheory

/-- Opaque placeholder for the representation category `Rep(H)` of a quasi-Hopf
algebra `H`. -/
opaque QuasiRepCat (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] : Type u := PUnit

/-- Placeholder category instance on `QuasiRepCat k H`. -/

end Thm_1_35_6

/-- Alias for `thm_1_35_6_reconstruction` (Theorem 1.35.6 reconstruction). -/

section DrinfeldTwist

/-- Drinfeld twist theorem: every finite-dimensional quasi-bialgebra admits a twist
trivializing its associator (so it becomes an honest bialgebra after twisting). -/

end DrinfeldTwist


section CocycleH2

universe uu vv

variable (G : Type uu) [Group G] (A : Type vv) [CommGroup A]

/-- The set of group 2-cocycles `G × G → A`. -/
def Cocycle2 := { μ : Cochain2 G A // IsCocycle2 G A μ }

/-- Setoid on 2-cocycles induced by cohomologousness (differing by a coboundary). -/
def cocycleCohomologousSetoid : Setoid (Cocycle2 G A) where
  r μ₁ μ₂ := Cohomologous2 G A μ₁.val μ₂.val
  iseqv := {
    refl := fun μ => ⟨fun _ => 1, fun g h => by simp [d1]⟩
    symm := fun {μ₁ μ₂} ⟨η, hη⟩ =>
      ⟨fun g => (η g)⁻¹, fun g h => by
        have := hη g h
        rw [this, d1_inv, mul_inv_cancel_right]⟩
    trans := fun {μ₁ μ₂ μ₃} ⟨η₁, h₁⟩ ⟨η₂, h₂⟩ =>
      ⟨fun g => η₁ g * η₂ g, fun g h => by
        rw [h₂ g h, h₁ g h]; simp [d1, mul_assoc, mul_comm, mul_left_comm]⟩
  }

/-- The second group cohomology `H²(G, A)`: cohomology classes of 2-cocycles. -/
def CocycleH2 := Quotient (cocycleCohomologousSetoid G A)

end CocycleH2
