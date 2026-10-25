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


noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
  PrimeSpectrum

universe u

namespace QCohSheaves

/-- Localization of an `R`-module at the powers of `f`, packaged as a `ModuleCat`. -/
def localizedModuleCat {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    ModuleCat.{u} R :=
  ModuleCat.of R (LocalizedModule (Submonoid.powers f) M)

/-- Image of `f ∈ R` under the natural isomorphism `R ≅ Γ(Spec R, 𝒪)`,
producing a global section of the structure sheaf of `Spec R`. -/
def toSpecGlobal {R : CommRingCat.{u}} (f : R) : Γ(Spec R, ⊤) :=
  (ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) f

/-- Open immersion of the basic open `D(f)` into `Spec R`. -/
def basicOpenInclusion {R : CommRingCat.{u}} (f : R) :
    ↑((Spec R).basicOpen (toSpecGlobal f)) ⟶ Spec R :=
  Scheme.Opens.ι ((Spec R).basicOpen (toSpecGlobal f))

end QCohSheaves
end
