/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec21NormalExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.NormalExtension
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NormalExtension

/-- Key technical step: if `x ∈ K` is locally regular at every height-one prime and
`c · x` already lies in `A`, then `c · x²` also lies in `A`. Used inductively to bound
denominators when proving integrality. -/
noncomputable def divByMap (b : A) : A →ₗ[A] K where
  toFun a := algebraMap A K a * (algebraMap A K b)⁻¹
  map_add' a₁ a₂ := by simp [add_mul]
  map_smul' r a := by
    simp only [RingHom.id_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring

/-- If `x ∈ K` lies in the localization of `A` at every height-one prime, then `x` is
integral over `A`. This is a key input to Hartogs/normal-domain results. -/
end NormalDomain

end Proposition39
