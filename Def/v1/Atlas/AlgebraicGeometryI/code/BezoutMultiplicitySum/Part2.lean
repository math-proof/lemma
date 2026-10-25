/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutLight
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- Local intersection multiplicity at a projective intersection point `p` of `f` and `g`,
defined as the `k`-dimension of the localisation of `k[x, y, z] / (⟨f⟩ + ⟨g⟩)` at the image
of `p`. -/
noncomputable def projLocalIntersectionMultiplicity
    (f g : MvPolynomial (Fin 3) k)
    (p : ProjectivePoint k f g) : ℕ := by
  let I := Ideal.span {f} ⊔ Ideal.span {g}
  let Q := p.P.map (Ideal.Quotient.mk I)
  have hI_le_P : I ≤ p.P := by
    apply sup_le
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr p.hf_mem)
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr p.hg_mem)
  have hQ_prime : Q.IsPrime := by
    haveI := p.hP_prime
    apply Ideal.map_isPrime_of_surjective
    · exact Ideal.Quotient.mk_surjective
    · intro x hx
      rw [Ideal.mk_ker] at hx
      exact hI_le_P hx
  exact @Module.finrank k (@Localization.AtPrime _ _ Q hQ_prime) _ _ _

end
