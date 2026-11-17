/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Structure.v1.Atlas.TensorCategories.code.QuasiBialgebra.Part2

@[expose] public section

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- The twisted coproduct `Δ^J(x) = J^{-1} Δ(x) J` (Definition 1.34.6). -/
noncomputable def QuasiBialgebraTwist.twistedComul
    {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
    [QuasiBialgebra R H] (tw : QuasiBialgebraTwist R H) (x : H) : H ⊗[R] H :=
  (↑tw.J⁻¹ : H ⊗[R] H) * QuasiBialgebra.comul x * (↑tw.J : H ⊗[R] H)

/-- The twisted associator
`Φ^J = (1 ⊗ J)^{-1} (Id ⊗ Δ)(J)^{-1} Φ (Δ ⊗ Id)(J) (J ⊗ 1)`
(Definition 1.34.6). -/
noncomputable def QuasiBialgebraTwist.twistedAssociator
    {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] (tw : QuasiBialgebraTwist R H) :
    H ⊗[R] (H ⊗[R] H) :=
  QuasiBialgebraTwist.embedRight R H (↑tw.J⁻¹ : H ⊗[R] H) *
  QuasiBialgebraTwist.idTensorComul R H qb.comul (↑tw.J⁻¹ : H ⊗[R] H) *
  (qb.Φ : H ⊗[R] (H ⊗[R] H)) *
  QuasiBialgebraTwist.comulTensorId R H qb.comul (↑tw.J : H ⊗[R] H) *
  QuasiBialgebraTwist.embedLeft R H (↑tw.J : H ⊗[R] H)

/-- Twist equivalence of quasi-bialgebras: two quasi-bialgebra structures on the
same underlying algebra `H` are twist equivalent if one is obtained from the other
by conjugation by a normalized invertible twist `J` (Definition 1.34.6). -/
def QuasiBialgebraTwistEquiv
    {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Algebra R H]
    (qb₁ qb₂ : QuasiBialgebra R H) : Prop :=
  ∃ J : (H ⊗[R] H)ˣ,

    QuasiBialgebraTwist.counitTensorId R H qb₁.counit (↑J : H ⊗[R] H) = 1 ∧
    QuasiBialgebraTwist.idTensorCounit R H qb₁.counit (↑J : H ⊗[R] H) = 1 ∧

    qb₂.counit = qb₁.counit ∧

    (∀ x : H, qb₂.comul x = (↑J⁻¹ : H ⊗[R] H) * qb₁.comul x * (↑J : H ⊗[R] H)) ∧

    (qb₂.Φ.val =
      QuasiBialgebraTwist.embedRight R H (↑J⁻¹ : H ⊗[R] H) *
      QuasiBialgebraTwist.idTensorComul R H qb₁.comul (↑J⁻¹ : H ⊗[R] H) *
      (qb₁.Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebraTwist.comulTensorId R H qb₁.comul (↑J : H ⊗[R] H) *
      QuasiBialgebraTwist.embedLeft R H (↑J : H ⊗[R] H))


