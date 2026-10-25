/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Class.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part2
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


namespace IsContractible

variable {S : Type*} [hc : IsContractible S]

/-- The retraction at time $t \in [0, 1]$: the convex combination
$(1 - t)\,\mathrm{embed}(s) + t\,\mathrm{embed}(\star)$ pulled back via `normalize`. -/
noncomputable def retraction (t : Set.Icc (0 : ℝ) 1) (s : S) : S :=
  hc.normalize ((1 - t.val) • hc.embed s + t.val • hc.embed hc.point)

end IsContractible
