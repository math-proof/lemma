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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part4


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The zero element of the graded Picard group (additive notation): the class of
the trivial fraction. -/
instance gradedPicardGroupZero (σ : Type*) (k : Type*) [Field k] :
    Zero (GradedPicardGroup σ k) :=
  ⟨⟦HomogFraction.one σ k⟧⟩

/-- Addition in the graded Picard group: induced from multiplication of fractions. -/
instance gradedPicardGroupAdd (σ : Type*) (k : Type*) [Field k] :
    Add (GradedPicardGroup σ k) :=
  ⟨Quotient.lift₂ (fun p q => ⟦p.mul σ k q⟧)
    (fun _ _ _ _ hp hq => Quotient.sound (mul_compat σ k hp hq))⟩

/-- Negation in the graded Picard group: induced from inversion of fractions. -/
instance gradedPicardGroupNeg (σ : Type*) (k : Type*) [Field k] :
    Neg (GradedPicardGroup σ k) :=
  ⟨Quotient.lift (fun p => ⟦p.inv σ k⟧)
    (fun _ _ h => Quotient.sound (inv_compat σ k h))⟩

end PicardProjective
end
