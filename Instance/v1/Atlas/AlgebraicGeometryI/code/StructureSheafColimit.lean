/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/StructureSheafColimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.StructureSheafColimit.Part2

@[expose] public section

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite


noncomputable section

namespace Lec6.RegularFunctions

/-- The function field of an integral scheme is a field. -/
instance functionField_field' (X : Scheme) [IsIntegral X] :
    Field X.functionField := inferInstance

end Lec6.RegularFunctions
end
