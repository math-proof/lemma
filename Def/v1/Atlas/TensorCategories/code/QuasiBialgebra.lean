/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


namespace QuasiBialgebra

variable (R : Type u) [CommSemiring R]

variable (H : Type v) [Semiring H] [Algebra R H]

/-- The algebra map `(Id ⊗ Δ) ∘ Δ : H → H ⊗ (H ⊗ H)` used in the quasi-coassociativity axiom. -/
noncomputable def idTensorComul (Δ : H →ₐ[R] H ⊗[R] H) :
    H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.map (AlgHom.id R H) Δ).comp Δ

/-- The algebra map `((Δ ⊗ Id) ∘ Δ)` reassociated to `H ⊗ (H ⊗ H)`, used in the
quasi-coassociativity axiom. -/
noncomputable def comulTensorId (Δ : H →ₐ[R] H ⊗[R] H) :
    H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  ((Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map Δ (AlgHom.id R H))).comp Δ

/-- The contraction `(Id ⊗ ε ⊗ Id) : H ⊗ (H ⊗ H) → H ⊗ H` used in stating
`(Id ⊗ ε ⊗ Id)(Φ) = 1 ⊗ 1`. -/
noncomputable def idCounitId (ε : H →ₐ[R] R) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    ((Algebra.TensorProduct.lid R H).toAlgHom.comp
      (Algebra.TensorProduct.map ε (AlgHom.id R H)))

/-- `(Id ⊗ Id ⊗ Δ)`, the map embedding into `H ⊗ (H ⊗ (H ⊗ H))`, used in the pentagon axiom. -/
noncomputable def idIdComul (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    (Algebra.TensorProduct.map (AlgHom.id R H) Δ)

/-- `(Δ ⊗ Id ⊗ Id)`, reassociated into `H ⊗ (H ⊗ (H ⊗ H))`, used in the pentagon axiom. -/
noncomputable def comulIdId (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  (Algebra.TensorProduct.assoc R R R H H (H ⊗[R] H)).toAlgHom.comp
    (Algebra.TensorProduct.map Δ (AlgHom.id R (H ⊗[R] H)))

/-- `(Id ⊗ Δ ⊗ Id)`, the middle inflation used in the pentagon axiom. -/
noncomputable def idComulId (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    ((Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
      (Algebra.TensorProduct.map Δ (AlgHom.id R H)))

/-- The right-tensoring embedding `H ⊗ (H ⊗ H) → H ⊗ (H ⊗ (H ⊗ H))` realizing
`Φ ⊗ 1` in the pentagon axiom. -/
noncomputable def embedPhiRight :
    H ⊗[R] (H ⊗[R] H) →ₐ[R] H ⊗[R] (H ⊗[R] (H ⊗[R] H)) :=
  Algebra.TensorProduct.map (AlgHom.id R H)
    (Algebra.TensorProduct.map (AlgHom.id R H)
      (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := H) (B := H)))

/-- Right multiplication by `c`, as an `R`-linear map. -/
def rmulMap (c : H) : H →ₗ[R] H := (LinearMap.mul R H).flip c

/-- The linear map `x ⊗ y ↦ S(x) · α · y`, used to express the left antipode axiom. -/
noncomputable def sAlphaMap (S : H →ₗ[R] H) (α_elem : H) : H ⊗[R] H →ₗ[R] H :=
  TensorProduct.lift ((LinearMap.mul R H).comp ((rmulMap R H α_elem).comp S))

/-- The linear map `x ⊗ y ↦ x · β · S(y)`, used to express the right antipode axiom. -/
noncomputable def betaSMap (S : H →ₗ[R] H) (β_elem : H) : H ⊗[R] H →ₗ[R] H :=
  LinearMap.mul' R H ∘ₗ TensorProduct.map (rmulMap R H β_elem) S

/-- The map `x ⊗ y ⊗ z ↦ x · β · S(y) · α · z` evaluating the antipode identity
`∑ Φ¹ β S(Φ²) α Φ³ = 1` from Proposition 1.35.1. -/
noncomputable def phiBetaSAlphaMap (S : H →ₗ[R] H) (α_elem β_elem : H) :
    H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
  LinearMap.mul' R H ∘ₗ
    TensorProduct.map (rmulMap R H β_elem) (sAlphaMap R H S α_elem)

/-- The map `x ⊗ y ⊗ z ↦ S(x) · α · y · β · S(z)` evaluating the dual antipode
identity `∑ S(Φ̄¹) α Φ̄² β S(Φ̄³) = 1` from Proposition 1.35.1. -/
noncomputable def phiInvSAlphaBetaSMap (S : H →ₗ[R] H) (α_elem β_elem : H) :
    H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
  LinearMap.mul' R H ∘ₗ
    TensorProduct.map ((rmulMap R H α_elem).comp S) (betaSMap R H S β_elem)

end QuasiBialgebra
