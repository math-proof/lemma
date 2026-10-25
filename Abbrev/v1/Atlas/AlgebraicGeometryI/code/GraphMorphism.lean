/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Graph morphism `Γ_f : X → X × Y` of `f : X → Y`, given by `(𝟙 X, f)`
(Def 18, Lec 7 in the absolute case). -/
noncomputable abbrev graphMor : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 X) f

end AlgebraicGeometry.Scheme
