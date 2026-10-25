/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part2


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The setoid on homogeneous fractions induced by the Pic equivalence relation. -/
instance homogFractionSetoid (σ : Type*) (k : Type*) [Field k] :
    Setoid (HomogFraction σ k) where
  r := HomogFraction.PicEquiv σ k
  iseqv := ⟨HomogFraction.PicEquiv.rfl' σ k,
            fun h => HomogFraction.PicEquiv.symm' σ k h,
            fun h1 h2 => HomogFraction.PicEquiv.trans' σ k h1 h2⟩

end PicardProjective
end
