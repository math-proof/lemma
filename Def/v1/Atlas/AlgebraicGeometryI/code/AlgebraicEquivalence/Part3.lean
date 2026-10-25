/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.AlgebraicEquivalence


noncomputable section

namespace AlgebraicEquivalence

open AlgebraicGeometry CategoryTheory Limits

universe u


namespace CartierDivisorGroup

/-- Two divisors `D₁`, `D₂` on `X` are *algebraically equivalent* if there is a connected
parameter scheme `T` over `S`, a divisor `𝒟` on `X ×_S T`, and two `S`-points `t₁, t₂` of `T`
whose pullbacks of `𝒟` are `D₁` and `D₂`. -/
def IsAlgebraicallyEquivalent {S X : Scheme.{u}} (sX : X ⟶ S)
    (D₁ D₂ : CartierDivisorGroup X) : Prop :=
  ∃ (T : ConnectedVariety S)
    (𝒟 : CartierDivisorGroup (pullback sX T.structureMorphism))
    (t₁ t₂ : SPoint T.structureMorphism),

    let ι₁ := pullback.lift (𝟙 X) (sX ≫ t₁.morphism)
      (by rw [Category.id_comp, Category.assoc, t₁.isSection, Category.comp_id])
    let ι₂ := pullback.lift (𝟙 X) (sX ≫ t₂.morphism)
      (by rw [Category.id_comp, Category.assoc, t₂.isSection, Category.comp_id])

    CartierDivisorGroup.pullback ι₁ 𝒟 = D₁ ∧
    CartierDivisorGroup.pullback ι₂ 𝒟 = D₂

/-- A divisor is *algebraically equivalent to zero* if it is algebraically equivalent to the zero
divisor. The subgroup of such divisors is the kernel of the map to the Néron-Severi group. -/
def IsAlgEquivZero {S X : Scheme.{u}} (sX : X ⟶ S)
    (D : CartierDivisorGroup X) : Prop :=
  IsAlgebraicallyEquivalent sX D 0

end CartierDivisorGroup
end AlgebraicEquivalence
end
