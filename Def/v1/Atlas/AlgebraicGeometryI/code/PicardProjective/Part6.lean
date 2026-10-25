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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The twisting sheaf O(d) in Pic(P^n), as the class of the d-th twist fraction. -/
def twistingSheafPow (n : ℕ) (k : Type*) [Field k] (d : ℤ) :
    GradedPicardGroup (Fin (n + 1)) k :=
  ⟦twistFraction n k d⟧

/-- The Serre twisting sheaf O(1) generating Pic(P^n) ≅ ℤ. -/
def twistingSheaf (n : ℕ) (k : Type*) [Field k] :
    GradedPicardGroup (Fin (n + 1)) k :=
  twistingSheafPow n k 1

end PicardProjective
end
