/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.PID
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec10SheavesP1
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1

namespace GrothendieckBirkhoff

/-- Over a PID, every submodule of `R^n` is free (used for the Grothendieck-Birkhoff splitting). -/
instance pid_submodule_Rn_free (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (n : ℕ) (N : Submodule R (Fin n → R)) :
    Module.Free R N :=
  inferInstance

/-- Euler characteristic of `O(n)` on `P^1`: `χ(O(n)) = dim H^0 - dim H^1`. -/
noncomputable def eulerCharP1 (k : Type) [Field k] (n : ℤ) : ℤ :=
  (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
  (Module.finrank k (SheafCohomology.H1 k n) : ℤ)

/-- Genus of a smooth plane curve of degree `d`: `g = (d - 1)(d - 2)/2`, the adjunction formula. -/
def genus_plane_curve (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2
