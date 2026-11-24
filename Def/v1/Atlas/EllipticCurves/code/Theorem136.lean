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

/-- The Frobenius discriminant $\Delta_\pi = t^2 - 4q \in \mathbb{Q}$, where $t$ is the trace of
Frobenius and $q = \#F$ is the cardinality of the base finite field (Section 13.6). -/
noncomputable def frobeniusDiscriminantQ (W : WeierstrassCurve.Affine F) : ℚ :=
  ((Hasse.traceFrobenius W : ℤ) ^ 2 - 4 * (Fintype.card F : ℤ) : ℤ)

/-- The defining polynomial $X^2 - \Delta_\pi$ of the endomorphism algebra, where
$\Delta_\pi = t^2 - 4q$ is the Frobenius discriminant. Adjoining a root yields an order
in the imaginary quadratic field $\mathbb{Q}(\sqrt{\Delta_\pi})$. -/
noncomputable def endPoly (W : WeierstrassCurve.Affine F) : ℚ[X] :=
  X ^ 2 - C (frobeniusDiscriminantQ W)

end EllipticCurve
