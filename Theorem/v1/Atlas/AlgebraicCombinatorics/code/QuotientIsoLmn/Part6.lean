/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part6
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

lemma gridYoungToWreathQuotient_wreathQuotientToGridYoung :
    ∀ q : WreathQuotient m n,
    gridYoungToWreathQuotient (wreathQuotientToGridYoung q) = q := by
  intro q; induction q using Quotient.inductionOn with
  | _ S =>
    show wreathQuotientMk (WreathOrbits.canonicalYoung S) = wreathQuotientMk S
    exact (wreathQuotientMk_eq_iff _ _).mpr
      ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
        (WreathOrbits.rowSizeMultiset_canonicalYoung S))

lemma wreathQuotientToGridYoung_gridYoungToWreathQuotient :
    ∀ D : GridYoungDiagram m n,
    wreathQuotientToGridYoung (gridYoungToWreathQuotient D) = D := by
  intro ⟨D, hD⟩; apply Subtype.ext
  exact WreathOrbits.gridYoung_unique (WreathOrbits.canonicalYoung_isGridYoung D) hD
    (WreathOrbits.rowSizeMultiset_canonicalYoung D)

lemma wreathQuotientToGridYoung_le_iff (a b : WreathQuotient m n) :
    wreathQuotientToGridYoung a ≤ wreathQuotientToGridYoung b ↔ a ≤ b := by
  constructor
  · intro h
    induction a using Quotient.inductionOn with | _ S =>
    induction b using Quotient.inductionOn with | _ T =>
    refine ⟨WreathOrbits.canonicalYoung S, WreathOrbits.canonicalYoung T, ?_, ?_, h⟩
    · exact (wreathQuotientMk_eq_iff _ _).mpr
        ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
          (WreathOrbits.rowSizeMultiset_canonicalYoung S))
    · exact (wreathQuotientMk_eq_iff _ _).mpr
        ((WreathOrbits.sameOrbit_iff_rowSizeMultiset_eq _ _).mpr
          (WreathOrbits.rowSizeMultiset_canonicalYoung T))
  · intro h
    obtain ⟨S', T', hS', hT', hsub⟩ := h
    induction a using Quotient.inductionOn with | _ S =>
    induction b using Quotient.inductionOn with | _ T =>
    change (WreathOrbits.canonicalYoung S) ⊆ (WreathOrbits.canonicalYoung T)
    have hSo : WreathOrbits.SameOrbit S S' :=
      (wreathQuotientMk_eq_iff S S').mp (hS' ▸ rfl)
    have hTo : WreathOrbits.SameOrbit T T' :=
      (wreathQuotientMk_eq_iff T T').mp (hT' ▸ rfl)
    rw [canonicalYoung_eq_of_sameOrbit hSo, canonicalYoung_eq_of_sameOrbit hTo]
    exact canonicalYoung_subset_of_subset hsub

end QuotientIsoLmn
