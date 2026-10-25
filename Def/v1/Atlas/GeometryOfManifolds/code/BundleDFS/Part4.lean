/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Complex.Basic
import Instance.v1.Atlas.GeometryOfManifolds.code.BundleDFS.Part3


noncomputable section

open scoped Manifold

open Bundle


namespace SpinCStructureDFS

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I ⊤ M]

/-- Sections $\Gamma(W^+)$ of the positive spinor bundle. -/
def SectionsPlus (spinc : SpinCStructureDFS I M) : Type _ :=
  SmoothSections spinc.SpinorPlusFiber

/-- Sections $\Gamma(W^-)$ of the negative spinor bundle. -/
def SectionsMinus (spinc : SpinCStructureDFS I M) : Type _ :=
  SmoothSections spinc.SpinorMinusFiber

end SpinCStructureDFS
end
