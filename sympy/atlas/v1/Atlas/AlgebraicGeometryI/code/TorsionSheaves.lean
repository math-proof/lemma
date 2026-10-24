/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.TorsionSheaf

variable {X : Scheme.{u}}

/-- A section `s` of a sheaf of `O_X`-modules `F` over `U` is a torsion
section iff it is annihilated by some nonzero scalar in `O_X(U)`. -/
def IsTorsionSection (F : X.Modules) (U : X.Opens)
    (s : (Scheme.Modules.presheaf F).obj (.op U)) : Prop :=
  ∃ r : X.presheaf.obj (.op U), r ≠ 0 ∧ r • s = 0

/-- A sheaf of `O_X`-modules is torsion iff every section over every
nonempty open is a torsion section. -/
def IsTorsionSheaf (F : X.Modules) : Prop :=
  ∀ (U : X.Opens) [Nonempty U] (s : (Scheme.Modules.presheaf F).obj (.op U)),
    IsTorsionSection F U s

/-- A sheaf of `O_X`-modules is torsion-free iff its only torsion section over
any nonempty open is the zero section. -/
def IsTorsionFreeSheaf (F : X.Modules) : Prop :=
  ∀ (U : X.Opens) [Nonempty U] (s : (Scheme.Modules.presheaf F).obj (.op U)),
    IsTorsionSection F U s → s = 0

section IntegralScheme

variable [IsIntegral X]

/-- The submodule of torsion sections of `F` over `U`. -/
noncomputable def torsionSections (F : X.Modules) (U : X.Opens) :
    Submodule (X.presheaf.obj (.op U)) ((Scheme.Modules.presheaf F).obj (.op U)) :=
  Submodule.torsion (X.presheaf.obj (.op U)) ((Scheme.Modules.presheaf F).obj (.op U))
