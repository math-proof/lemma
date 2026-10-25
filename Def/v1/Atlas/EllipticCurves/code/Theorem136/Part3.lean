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
import Instance.v1.Atlas.EllipticCurves.code.Theorem136
open Module Polynomial
open scoped TensorProduct

universe u


namespace EllipticCurve

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The (noncommutative) ring instance on the endomorphism algebra obtained by forgetting
commutativity. -/
@[instance, reducible] noncomputable def EndAlgebra.instRing
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : Ring (EndAlgebra W) :=
  (EndAlgebra.instCommRing W).toRing

/-- The $\mathbb{Q}$-algebra structure on the endomorphism algebra inherited from
`AdjoinRoot`. -/
@[instance, reducible] noncomputable def EndAlgebra.instAlgebra
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : Algebra ℚ (EndAlgebra W) :=
  inferInstanceAs (Algebra ℚ (AdjoinRoot (endPoly W)))

end EllipticCurve
