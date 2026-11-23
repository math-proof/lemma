/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/BundleDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.Analysis.Complex.Basic
public import Instance.v1.Atlas.GeometryOfManifolds.code.BundleDFS.Part3

@[expose] public section

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
