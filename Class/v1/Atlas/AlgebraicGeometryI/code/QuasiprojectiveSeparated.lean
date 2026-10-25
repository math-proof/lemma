/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QuasiprojectiveSeparated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


noncomputable section

universe u

namespace QuasiprojectiveSeparated

/-- Def 6 (Lec 3): `X` is quasi-projective if it admits a locally closed immersion
into some projective scheme `Proj 𝒜`. -/
class IsQuasiProjective (X : Scheme.{u}) : Prop where
  exists_locally_closed_immersion :
    ∃ (σ : Type u) (A : Type u) (_ : CommRing A) (_ : SetLike σ A)
      (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
      (Z : Scheme.{u}) (f : X ⟶ Z) (g : Z ⟶ Proj 𝒜),
      IsClosedImmersion f ∧ IsOpenImmersion g

end QuasiprojectiveSeparated
end
