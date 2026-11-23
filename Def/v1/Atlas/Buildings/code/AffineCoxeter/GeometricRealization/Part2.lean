/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/GeometricRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
public import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Basic
public import Structure.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization.Part2

@[expose] public section

set_option linter.unusedSectionVars false


noncomputable section

open Finset BigOperators

attribute [instance] CoxeterComplexGeometricRealization.topSpace

/-- Forgetting the linear/Euclidean structure: every affine geometric realization gives an abstract
geometric realization with the same chambers and fundamental domain. -/
def AffineGeometricRealization.toCoxeterComplex {W : Type*} [Group W] {S : Set W}
    {ι : Type*} [Fintype ι] (A : AffineGeometricRealization W S ι) :
    CoxeterComplexGeometricRealization W S where
  carrier := EuclideanSpace ℝ ι
  chamberMap := fun w => A.action w '' A.fundamentalChamber
  fundamentalDomain := A.fundamentalChamber

end
