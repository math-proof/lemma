/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientPoset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.SpernerProperty
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Card
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset.Part4
open Finset MulAction
open scoped Pointwise


section RankSymmetry

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

noncomputable def quotientPosetCompl :
    QuotientPoset n G → QuotientPoset n G :=
  Quotient.lift
    (fun S => Quotient.mk (orbitRel G _) (Finset.univ \ S))
    (by
      intro S T h
      apply Quotient.sound
      show (orbitRel G (Finset (Fin n))).r (Finset.univ \ S) (Finset.univ \ T)
      have hST : (orbitRel G (Finset (Fin n))).r S T := h
      rw [orbitRel_apply] at hST ⊢
      obtain ⟨g, hg⟩ := hST
      refine ⟨g, ?_⟩

      change g • (Finset.univ \ T) = Finset.univ \ S
      rw [smul_compl_eq]
      change g • T = S at hg
      rw [hg])

end RankSymmetry
