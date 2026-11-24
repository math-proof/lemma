module
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.QuaternionBasis
public import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
public import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndomorphismAlgebra
public import Instance.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra.Part2
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.SimpleRing.Basic
public import Class.v1.Atlas.EllipticCurves.code.EndAlgClassification
open Module
open scoped Quaternion TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgClassification.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The reduced trace `tr(a) = N(a + 1) - N(a) - 1`, induced by the reduced norm. -/
noncomputable def traceMap (a : A) : ℚ :=
  normMap (a + 1) - normMap a - 1

end PositiveDefiniteInvolutionAlgebra
