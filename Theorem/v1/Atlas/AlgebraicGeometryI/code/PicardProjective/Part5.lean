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
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part3


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- Two homogeneous fractions with identical components are equivalent. -/
lemma ring_assoc_equiv (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k)
    (hn : p.num = q.num) (hd : p.den = q.den)
    (_ : p.ndeg = q.ndeg) (_ : p.ddeg = q.ddeg) :
    p.PicEquiv σ k q := by
  refine ⟨1, 1, 0, 0, one_ne_zero, one_ne_zero,
    isHomogeneous_one σ k, isHomogeneous_one σ k, rfl, ?_⟩
  rw [mul_one, mul_one, hn, hd]

end PicardProjective
end
