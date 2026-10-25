/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/GeometricRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Structure.v1.Atlas.Buildings.code.AffineCoxeter.GeometricRealization.Part2
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
