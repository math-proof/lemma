/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/StructureSheafColimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.Topology.Sheaves.Stalks

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

noncomputable section

namespace Lec6.RegularFunctions

example (R : Type*) [CommRing R] :
    TopCat.LocalPredicate (StructureSheaf.Localizations (R := R) R) :=
  StructureSheaf.isLocallyFraction R R

example (R : Type*) [CommRing R] :
    TopCat.Sheaf (Type _) (PrimeSpectrum.Top R) :=
  structureSheafInType R R

example {X : TopCat} (F : X.Presheaf CommRingCat) (U : Opens X) (x : X) (hx : x ∈ U) :
    F.obj (op U) ⟶ F.stalk x :=
  F.germ U x hx

/-- The stalk of the structure sheaf of `Spec R` at a prime `𝔭` is canonically
the localization of `R` at `𝔭`. -/
def stalk_iso_localization (R : Type*) [CommRing R] (𝔭 : PrimeSpectrum R) :
    Localization.AtPrime 𝔭.asIdeal ≃ₐ[R]
      ↑((structurePresheafInCommRingCat R).stalk 𝔭) :=
  StructureSheaf.stalkIso R 𝔭

example (X : Scheme) [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    Γ(X, U) ⟶ X.functionField :=
  X.germToFunctionField U

example (R : CommRingCat) [IsDomain R] :
    IsFractionRing R (Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

example (X : Scheme) : TopCat.Sheaf CommRingCat ↑X.toPresheafedSpace :=
  X.sheaf

/-- The function field of an integral scheme is a field. -/
instance functionField_field' (X : Scheme) [IsIntegral X] :
    Field X.functionField := inferInstance

end Lec6.RegularFunctions
