/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorem.v1.Atlas.EllipticCurves.code.Theorem136
open Module Polynomial
open scoped TensorProduct

universe u


namespace EllipticCurve

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The endomorphism algebra $\mathrm{End}^0(E) = \mathbb{Q}[X]/(X^2 - \Delta_\pi)$ presented
abstractly as the quotient algebra adjoining a square root of the Frobenius discriminant
(Theorem 13.6). -/
noncomputable def EndAlgebra (W : WeierstrassCurve.Affine F) : Type :=
  AdjoinRoot (endPoly W)

end EllipticCurve
