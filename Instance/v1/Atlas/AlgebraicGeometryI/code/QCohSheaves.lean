/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.QCohSheaves

@[expose] public section

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
