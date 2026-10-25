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
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part5


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The twist O(d) has degree d. -/
lemma twistFraction_degree (n : ℕ) (k : Type*) [Field k] (d : ℤ) :
    (twistFraction n k d).degree (Fin (n + 1)) k = d := by
  unfold twistFraction HomogFraction.degree
  split
  · simp only [Int.toNat_of_nonneg (by omega : 0 ≤ d)]
    omega
  · simp only [Int.toNat_of_nonneg (by omega : 0 ≤ -d)]
    omega

end PicardProjective
end
