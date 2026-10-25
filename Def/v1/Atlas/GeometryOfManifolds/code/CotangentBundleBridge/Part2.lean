/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CotangentBundleBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Abbrev.v1.Atlas.GeometryOfManifolds.code.CotangentBundleBridge
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff
open DifferentialFormSpace


universe u


section CotangentBundleDFSTypes

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type u} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H)

variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I ∞ M]

/-- The `DifferentialFormSpace` structure on $T^*M$, induced from its manifold structure. -/
@[reducible]
noncomputable def cotangentBundleDFSInst :
    DifferentialFormSpace (CotangentBundleΩ I M) (CotangentBundleVF I M) :=
  manifoldDFS (cotangentBundleModel I) (CotangentBundle I M)


end CotangentBundleDFSTypes
