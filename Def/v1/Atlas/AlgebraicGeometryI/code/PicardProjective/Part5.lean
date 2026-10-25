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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part6


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The degree map as an additive group homomorphism Pic(P^n) → ℤ. -/
def GradedPicardGroup.degreeHom (σ : Type*) (k : Type*) [Field k] :
    GradedPicardGroup σ k →+ ℤ where
  toFun := GradedPicardGroup.degreeMap σ k
  map_zero' := by
    simp only [GradedPicardGroup.degreeMap]
    change Quotient.lift (HomogFraction.degree σ k) _ ⟦HomogFraction.one σ k⟧ = 0
    simp [HomogFraction.degree, HomogFraction.one]
  map_add' := degreeMap_add σ k


/-- The homogeneous fraction representing the d-th twist O(d) on P^n. -/
def twistFraction (n : ℕ) (k : Type*) [Field k] (d : ℤ) :
    HomogFraction (Fin (n + 1)) k :=
  if hd : 0 ≤ d then
    { num := (X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ d.toNat
      den := 1
      num_ne := pow_ne_zero _ (X_ne_zero _)
      den_ne := one_ne_zero
      ndeg := d.toNat
      ddeg := 0
      nhom := by simpa using (isHomogeneous_X k (0 : Fin (n + 1))).pow d.toNat
      dhom := isHomogeneous_one _ k }
  else
    { num := 1
      den := (X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) k) ^ (-d).toNat
      num_ne := one_ne_zero
      den_ne := pow_ne_zero _ (X_ne_zero _)
      ndeg := 0
      ddeg := (-d).toNat
      nhom := isHomogeneous_one _ k
      dhom := by simpa using (isHomogeneous_X k (0 : Fin (n + 1))).pow (-d).toNat }

end PicardProjective
end
