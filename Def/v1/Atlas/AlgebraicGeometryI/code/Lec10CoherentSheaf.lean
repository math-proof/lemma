/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10CoherentSheaf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec10CoherentSheaf
open AlgebraicGeometry CategoryTheory


/-- Algebraic counterpart: an `R`-module `M` is "coherent" in our sense iff it is
finitely generated as an `R`-module. -/
def IsCoherentModule (R : Type*) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Prop :=
  Module.Finite R M

