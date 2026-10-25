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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.StructureSheafColimit
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite


noncomputable section

namespace Lec6.RegularFunctions

/-- The stalk of the structure sheaf of `Spec R` at a prime `𝔭` is canonically
the localization of `R` at `𝔭`. -/
def stalk_iso_localization (R : Type*) [CommRing R] (𝔭 : PrimeSpectrum R) :
    Localization.AtPrime 𝔭.asIdeal ≃ₐ[R]
      ↑((structurePresheafInCommRingCat R).stalk 𝔭) :=
  StructureSheaf.stalkIso R 𝔭

end Lec6.RegularFunctions
end
