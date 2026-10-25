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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner.Part2
set_option autoImplicit false


noncomputable section

open scoped Classical Pointwise

open SpernerProperty YoungLattice YoungLattice.Lmn

open QuotientIsoLmn GroupActions WreathOrbits Finset MulAction

namespace YoungLattice.Lmn

variable {m n : ℕ}

set_option maxHeartbeats 1600000 in
def quotientPosetIsoLmn (m n : ℕ) :
    letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
    letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
    { e : QuotientPoset (m * n) (wreathSubgroup m n) ≃o Lmn m n //
      ∀ p, grade ℕ (e p) = grade ℕ p } := by
  letI := quotientPoset_gradeMinOrder (m * n) (wreathSubgroup m n)
  letI := quotientPoset_gradedPoset (m * n) (wreathSubgroup m n)
  let e := (quotientPosetIsoWreathQuotient m n).trans (wreathQuotientIsoLmn m n)
  refine ⟨e, fun p => ?_⟩
  induction p using Quotient.inductionOn with
  | _ A =>
    have lhs_eq : grade ℕ (e (@Quotient.mk _ (orbitRel _ _) A)) = A.card := by
      show grade ℕ ((wreathQuotientIsoLmn m n)
        ((quotientPosetIsoWreathQuotient m n) (@Quotient.mk _ (orbitRel _ _) A))) = A.card
      have hbridge : (quotientPosetIsoWreathQuotient m n) (@Quotient.mk _ (orbitRel _ _) A) =
          wreathQuotientMk (A.image finProdFinEquiv.symm) := by
        show (quotientPosetEquivWreathQuotient m n) (@Quotient.mk _ (orbitRel _ _) A) = _
        simp [quotientPosetEquivWreathQuotient]
      rw [hbridge]
      exact grade_composed_iso A
    have rhs_eq : grade ℕ (@Quotient.mk _ (orbitRel (wreathSubgroup m n)
        (Finset (Fin (m * n)))) A) = A.card := rfl
    rw [lhs_eq, rhs_eq]

end YoungLattice.Lmn
end
