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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part8


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The fundamental identification Pic(P^n) ≅ ℤ as additive groups, via the degree map. -/
def gradedPicardGroup_equiv_int (k : Type*) [Field k] (n : ℕ) :
    GradedPicardGroup (Fin (n + 1)) k ≃+ ℤ :=
  AddEquiv.ofBijective
    (GradedPicardGroup.degreeHom (Fin (n + 1)) k)
    ⟨degreeHom_injective (Fin (n + 1)) k,
     degreeHom_surjective n k⟩

end PicardProjective
end
