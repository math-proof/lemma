/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part13


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (N : ℕ)
    (hdegree : ons_finsuppTotalDegree m ≤ N) :
    ons_decFormalFirstReturnCoeff L a b d m =
      ∑ atom : ons_DecFirstReturnAtomBounded L d N,
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom
        else 0 := by
  classical
  rw [ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms]
  let embedding := ons_decBoundedAtomEmbedding
    (L := L) (d := d) hdegree
  let term : ons_DecFirstReturnAtomBounded L d N → ℂ :=
    fun atom ↦ if ons_decBoundedAtomExponent atom = m then
      ons_decBoundedAtomWeight L a b atom else 0
  calc
    (∑ atom : ons_DecFirstReturnAtomBounded L d
        (ons_finsuppTotalDegree m),
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom else 0) =
        ∑ atom ∈ Finset.univ.map embedding, term atom := by
          rw [Finset.sum_map]
          rfl
    _ = ∑ atom : ons_DecFirstReturnAtomBounded L d N, term atom := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro atom hatom hnot
      by_cases hexponent : ons_decBoundedAtomExponent atom = m
      · exfalso
        apply hnot
        rw [Finset.mem_map]
        have hlength := ons_decLoopExponent_length_le L atom.2.1
        change atom.1.val + 1 ≤
          ons_finsuppTotalDegree (ons_decBoundedAtomExponent atom) at hlength
        rw [hexponent] at hlength
        let rsmall : Fin (ons_finsuppTotalDegree m) :=
          ⟨atom.1.val, by omega⟩
        let small : ons_DecFirstReturnAtomBounded L d
            (ons_finsuppTotalDegree m) :=
          ⟨rsmall, atom.2⟩
        refine ⟨small, Finset.mem_univ _, ?_⟩
        apply Sigma.ext
        · exact Fin.ext rfl
        · rfl
      · simp [term, hexponent]
    _ = _ := rfl

end StatMech.Onsager
