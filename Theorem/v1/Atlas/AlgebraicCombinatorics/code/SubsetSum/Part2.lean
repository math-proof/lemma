/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLatticeSperner
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QBinomial
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner.Part3
import Def.v1.Atlas.AlgebraicCombinatorics.code.QBinomial.Part2
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Def.v1.Atlas.AlgebraicCombinatorics.code.SubsetSum.Part2
set_option autoImplicit false

open SpernerProperty YoungLattice YoungLattice.Lmn Finset


namespace SubsetSum

lemma idxFun_strictMono
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S) :
    StrictMono (idxFun S n hScard T k hTcard hTsub) := by
  intro a b hab
  simp only [idxFun]
  apply (S.orderIsoOfFin hScard).symm.strictMono
  simp only [Subtype.mk_lt_mk]
  exact (T.orderEmbOfFin hTcard).strictMono hab

lemma idxVal_ge
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (r : Fin k) : r.val ≤ idxVal S n hScard T k hTcard hTsub r := by
  simp only [idxVal]
  have hsm : StrictMono (fun r => (idxFun S n hScard T k hTcard hTsub r).val) :=
    fun a b hab => (idxFun_strictMono S n hScard T k hTcard hTsub).lt_iff_lt.mpr hab
  have h0 : 0 ≤ (idxFun S n hScard T k hTcard hTsub ⟨0, r.pos⟩).val := Nat.zero_le _
  by_cases hr0 : r.val = 0
  · have : r = ⟨0, r.pos⟩ := Fin.ext (by omega); rw [this]; omega
  · have h0r : (⟨0, r.pos⟩ : Fin k) ≤ r := Fin.mk_le_mk.mpr (by omega)
    have := strictMono_fin_add_le hsm ⟨0, r.pos⟩ r h0r
    simp at this; omega

lemma idxVal_bound
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (hkn : k ≤ n)
    (r : Fin k) : idxVal S n hScard T k hTcard hTsub r - r.val ≤ n - k := by
  simp only [idxVal]
  have hk_pos : 0 < k := r.pos
  have hsm : StrictMono (fun r => (idxFun S n hScard T k hTcard hTsub r).val) :=
    fun a b hab => (idxFun_strictMono S n hScard T k hTcard hTsub).lt_iff_lt.mpr hab
  have hbound : (idxFun S n hScard T k hTcard hTsub r).val < n := (idxFun S n hScard T k hTcard hTsub r).isLt
  by_cases hrk : r.val = k - 1
  · have : r = ⟨k - 1, by omega⟩ := Fin.ext (by omega); rw [this]; omega
  · have hlt : r < ⟨k - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have hlast_bound : (idxFun S n hScard T k hTcard hTsub ⟨k - 1, by omega⟩).val < n :=
      (idxFun S n hScard T k hTcard hTsub ⟨k - 1, by omega⟩).isLt
    have := strictMono_fin_add_le hsm r ⟨k - 1, by omega⟩ (le_of_lt hlt)
    simp at this; omega

end SubsetSum
