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
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part3


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The degree function is compatible with the Pic equivalence relation: equivalent
homogeneous fractions have the same degree. -/
lemma degree_compat (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k) (h : p.PicEquiv σ k q) :
    p.degree σ k = q.degree σ k := by
  obtain ⟨a, b, da, db, ha, hb, hah, hbh, hd, hass⟩ := h
  unfold HomogFraction.degree
  have lhs_ne : p.num * b * q.den ≠ 0 := mul_ne_zero (mul_ne_zero p.num_ne hb) q.den_ne
  have rhs_ne : q.num * a * p.den ≠ 0 := mul_ne_zero (mul_ne_zero q.num_ne ha) p.den_ne
  have lhs_hom : (p.num * b * q.den).IsHomogeneous (p.ndeg + db + q.ddeg) :=
    (p.nhom.mul hbh).mul q.dhom
  have rhs_hom : (q.num * a * p.den).IsHomogeneous (q.ndeg + da + p.ddeg) :=
    (q.nhom.mul hah).mul p.dhom
  have := associated_homogeneous_same_degree rhs_ne lhs_hom rhs_hom hass
  omega

end PicardProjective
end
