/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection
import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part2
open Matrix


noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

/-- A *compact surface*: a compact, connected, Hausdorff topological space
with a charted-space structure on `ℝ²` that makes it a `C⁰` manifold. This
is the geometric setting for the classification of surfaces. -/
structure CompactSurface where
  toTopCat : TopCat.{0}
  compact : CompactSpace toTopCat
  connected : ConnectedSpace toTopCat
  t2 : T2Space toTopCat
  charted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) toTopCat
  isManifold : letI := charted;
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) 0 toTopCat

end SurfacesAndBilinearForms
end
