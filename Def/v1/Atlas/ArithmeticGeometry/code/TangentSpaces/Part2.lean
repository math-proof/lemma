module
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.FunctionFieldGenerators
public import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part5
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProductVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.CotangentLocal
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularFunctions
public import Def.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part3
public import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part9
public import Theorem.v1.Atlas.ArithmeticGeometry.code.TangentSpaces


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TangentSpaces.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Matrix Module Submodule LinearMap FiniteDimensional MvPolynomial

section GeometricTangentSpace

variable {k : Type*} [Field k] {n : ℕ}

def functionField (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) : Type _ :=
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain' k N V hV

  FractionRing (AffineCoordinateRingBar V)

@[reducible] noncomputable def functionField.instField (k : Type*) [Field k] (N : ℕ)
    (V : Set (AffineSpace_k k N)) (hV : IsAffineVariety k N V) :
    Field (functionField k N V hV) := by
  unfold functionField
  letI : IsDomain (AffineCoordinateRingBar V) := coordinateRingBar_isDomain' k N V hV
  exact FractionRing.field (AffineCoordinateRingBar V)

end GeometricTangentSpace
end
