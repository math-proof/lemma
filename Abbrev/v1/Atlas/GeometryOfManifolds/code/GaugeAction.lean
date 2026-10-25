/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/GaugeAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
set_option autoImplicit false


noncomputable section

/-- The Seiberg–Witten gauge group $\mathcal{G} = C^\infty(M, S^1)$ on a manifold $M$. -/
abbrev SWGaugeGroup (M : Type*) [TopologicalSpace M] := C(M, Circle)

end
