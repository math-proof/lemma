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
public import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohSheaves

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
  PrimeSpectrum

universe u

namespace QCohSheaves

/-- The adjunction `tilde ⊣ Γ` between modules over `R` and sheaves of modules
on `Spec R`. -/
def tilde_gamma_adjunction (R : CommRingCat.{u}) :
    tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- Predicate version of quasi-coherence for a sheaf of modules on a scheme. -/
def IsQuasicoherentSheaf {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent

end QCohSheaves
end
