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
public import Structure.v1.Atlas.GeometryOfManifolds.code.BundleDFS.Part2

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

/-- The positive spinor fiber $W^+_x$ inherits an abelian group structure. -/
instance instACGPlus (spinc : SpinCStructureDFS I M) (x : M) :
    AddCommGroup (spinc.SpinorPlusFiber x) := spinc.instACG_plus x

/-- The positive spinor fiber $W^+_x$ is a complex vector space. -/
instance instModPlus (spinc : SpinCStructureDFS I M) (x : M) :
    Module ℂ (spinc.SpinorPlusFiber x) := spinc.instMod_plus x

/-- The negative spinor fiber $W^-_x$ inherits an abelian group structure. -/
instance instACGMinus (spinc : SpinCStructureDFS I M) (x : M) :
    AddCommGroup (spinc.SpinorMinusFiber x) := spinc.instACG_minus x

/-- The negative spinor fiber $W^-_x$ is a complex vector space. -/
instance instModMinus (spinc : SpinCStructureDFS I M) (x : M) :
    Module ℂ (spinc.SpinorMinusFiber x) := spinc.instMod_minus x

end SpinCStructureDFS
end
