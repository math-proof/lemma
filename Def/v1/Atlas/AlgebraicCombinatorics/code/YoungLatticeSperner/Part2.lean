/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungLatticeSperner.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part7
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QuotientIsoLmn
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty YoungLattice YoungLattice.Lmn

open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction

namespace YoungLattice.Lmn

variable {m n : ℕ}

set_option maxHeartbeats 1600000 in
noncomputable def quotientPosetEquivWreathQuotient (m n : ℕ) :
    QuotientPoset (m * n) (wreathSubgroup m n) ≃ WreathQuotient m n where
  toFun := Quotient.lift
    (fun (A : Finset (Fin (m * n))) => wreathQuotientMk (A.image finProdFinEquiv.symm))
    (fun (A B : Finset (Fin (m * n))) (hab : _) => by
      rw [wreathQuotientMk_eq_iff]
      obtain ⟨g, rfl⟩ := hab
      exact (sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
        ((sameOrbit_iff_rowSizeMultiset_eq _ _).mp
          (sameOrbit_of_wreathSubgroup_orbit B g)).symm)
  invFun := Quotient.lift
    (fun (S : Finset (Fin m × Fin n)) => @Quotient.mk _ (orbitRel (wreathSubgroup m n) _)
      (S.image finProdFinEquiv))
    (fun (S T : Finset (Fin m × Fin n)) (hST : _) => by
      apply Quotient.sound
      obtain ⟨g, hg⟩ := wreathSubgroup_orbit_of_sameOrbit T S
        ((sameOrbit_iff_rowSizeMultiset_eq T S).mpr
          ((sameOrbit_iff_rowSizeMultiset_eq S T).mp hST).symm)
      exact ⟨g, hg⟩)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ A =>
      simp only [Quotient.lift_mk, wreathQuotientMk]
      congr 1; rw [Finset.image_image]; simp
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ S =>
      simp only [Quotient.lift_mk, wreathQuotientMk]
      congr 1; rw [Finset.image_image]; simp

set_option maxHeartbeats 1600000 in
noncomputable def quotientPosetIsoWreathQuotient (m n : ℕ) :
    QuotientPoset (m * n) (wreathSubgroup m n) ≃o WreathQuotient m n where
  toEquiv := quotientPosetEquivWreathQuotient m n
  map_rel_iff' := by
    intro a b
    let f := quotientPosetEquivWreathQuotient m n
    constructor
    · rintro ⟨S, T, hS, hT, hsub⟩
      have ha : a = @Quotient.mk _ (orbitRel (wreathSubgroup m n) _)
          (S.image finProdFinEquiv) := by
        rw [← f.symm_apply_apply a, ← hS]
        show f.symm (wreathQuotientMk S) = _
        simp only [f, quotientPosetEquivWreathQuotient, Equiv.coe_fn_symm_mk,
          wreathQuotientMk, Quotient.lift_mk]
      have hb : b = @Quotient.mk _ (orbitRel (wreathSubgroup m n) _)
          (T.image finProdFinEquiv) := by
        rw [← f.symm_apply_apply b, ← hT]
        show f.symm (wreathQuotientMk T) = _
        simp only [f, quotientPosetEquivWreathQuotient, Equiv.coe_fn_symm_mk,
          wreathQuotientMk, Quotient.lift_mk]
      exact ⟨S.image finProdFinEquiv, T.image finProdFinEquiv, ha.symm, hb.symm,
        Finset.image_subset_image hsub⟩
    · rintro ⟨S, T, hS, hT, hsub⟩
      refine ⟨S.image finProdFinEquiv.symm, T.image finProdFinEquiv.symm, ?_, ?_,
        Finset.image_subset_image hsub⟩
      · subst hS; rfl
      · subst hT; rfl

end YoungLattice.Lmn
end
