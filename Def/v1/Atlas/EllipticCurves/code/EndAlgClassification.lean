/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.QuaternionBasis
import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndomorphismAlgebra
import Instance.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra.Part2
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.SimpleRing.Basic
import Class.v1.Atlas.EllipticCurves.code.EndAlgClassification
open Module
open scoped Quaternion TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- The reduced trace `tr(a) = N(a + 1) - N(a) - 1`, induced by the reduced norm. -/
noncomputable def traceMap (a : A) : ℚ :=
  normMap (a + 1) - normMap a - 1

end PositiveDefiniteInvolutionAlgebra
