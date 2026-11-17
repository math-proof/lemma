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
public import Def.v1.Atlas.AlgebraicGeometryI.code.StructureSheafColimit
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

public section

noncomputable section

namespace Lec6.RegularFunctions

example (X : Scheme) [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    Γ(X, U) ⟶ X.functionField :=
  X.germToFunctionField U

example (R : CommRingCat) [IsDomain R] :
    IsFractionRing R (Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

example (X : Scheme) : TopCat.Sheaf CommRingCat ↑X.toPresheafedSpace :=
  X.sheaf

end Lec6.RegularFunctions
end
