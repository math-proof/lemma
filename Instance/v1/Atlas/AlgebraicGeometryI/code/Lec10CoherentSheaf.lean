/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10CoherentSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Class.v1.Atlas.AlgebraicGeometryI.code.Lec10CoherentSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory


namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}
  [∀ X, (J.over X).HasSheafCompose (CategoryTheory.forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

attribute [instance] IsCoherent.isQuasicoherent IsCoherent.isFiniteType

instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] : M.IsCoherent where
  isQuasicoherent := inferInstance
  isFiniteType := inferInstance

end SheafOfModules
