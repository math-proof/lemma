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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The (divisor) class group of a polynomial ring over a field is trivial. -/
instance classGroup_mvPolynomial_subsingleton (k : Type*) [Field k] (σ : Type*) :
    Subsingleton (ClassGroup (MvPolynomial σ k)) := inferInstance

/-- The class group of the univariate polynomial ring k[x] is trivial. -/
instance classGroup_polynomial_subsingleton (k : Type*) [Field k] :
    Subsingleton (ClassGroup (Polynomial k)) := inferInstance

/-- The class group of k[x_1,...,x_n] is the trivial group with a unique element. -/
instance classGroup_mvPolynomial_unique (k : Type*) [Field k] (n : ℕ) :
    Unique (ClassGroup (MvPolynomial (Fin n) k)) := Unique.mk' _

end PicardProjective
end
