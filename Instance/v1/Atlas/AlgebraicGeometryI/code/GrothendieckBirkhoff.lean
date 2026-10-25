/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrothendieckBirkhoff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.PID
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec10SheavesP1
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1.Part3


namespace GrothendieckBirkhoff

/-- Over a PID, every submodule of `R^n` is free (used for the Grothendieck-Birkhoff splitting). -/
instance pid_submodule_Rn_free (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (n : ℕ) (N : Submodule R (Fin n → R)) :
    Module.Free R N :=
  inferInstance

end GrothendieckBirkhoff
