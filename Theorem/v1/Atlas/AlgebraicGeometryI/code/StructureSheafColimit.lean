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

end Lec6.RegularFunctions
end
