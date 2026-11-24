module
public import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.PointCounting
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
public import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
public import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.v1.Atlas.EllipticCurves.code.Theorem136.Part2
open Module Polynomial
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


namespace EllipticCurve

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The endomorphism algebra inherits the commutative ring structure from `AdjoinRoot`. -/
noncomputable instance EndAlgebra.instCommRing
    (W : WeierstrassCurve.Affine F) : CommRing (EndAlgebra W) :=
  inferInstanceAs (CommRing (AdjoinRoot (endPoly W)))

end EllipticCurve
