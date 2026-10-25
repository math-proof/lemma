/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8CompleteVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion
open AlgebraicGeometry CategoryTheory Limits

universe u


namespace Formalization.Lec8CompleteVarieties

/-- A morphism `f : X ⟶ Y` is complete if it is separated and
universally closed (Lec 8, Def 19). -/
class IsComplete {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isSeparated : IsSeparated f
  universallyClosed : UniversallyClosed f


end Formalization.Lec8CompleteVarieties
