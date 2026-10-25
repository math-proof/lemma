/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.QCohSheaves


noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
  PrimeSpectrum

universe u

namespace QCohSheaves

/-- Prop 16 (Lec 12) input: applying tilde to `M`, then restricting and pushing
forward along `D(f) ↪ Spec R`, gives a sheaf whose `fromTildeΓ` counit is an
isomorphism. -/
instance tilde_isQuasicoherent_goal94 {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

end QCohSheaves
end
