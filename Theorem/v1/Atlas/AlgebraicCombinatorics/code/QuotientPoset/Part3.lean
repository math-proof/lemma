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
import Instance.v1.Atlas.AlgebraicCombinatorics.code.QuotientPoset
open Finset MulAction
open scoped Pointwise


namespace SpernerProperty

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}

theorem quotientPosetRank_strictMono (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) :
    StrictMono (quotientPosetRank n G) := by
  classical
  intro a b hab
  obtain ⟨S, T, hS, hT, hsub⟩ := hab.le
  have hne : a ≠ b := ne_of_lt hab
  have hST : S ≠ T := by
    intro heq; subst heq; exact hne (hS ▸ hT)
  have hss : S ⊂ T := lt_of_le_of_ne hsub (by intro h; exact hST h)
  calc quotientPosetRank n G a
      = S.card := by rw [← hS]; rfl
    _ < T.card := Finset.card_lt_card hss
    _ = quotientPosetRank n G b := by rw [← hT]; rfl

theorem quotientPosetRank_covBy (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    {a b : QuotientPoset n G}
    (hcov : a ⋖ b) : quotientPosetRank n G a ⋖ quotientPosetRank n G b := by
  classical
  rw [Nat.covBy_iff_add_one_eq]
  have hlt := (quotientPosetRank_strictMono n G) hcov.lt
  by_contra h
  have hgap : quotientPosetRank n G a + 2 ≤ quotientPosetRank n G b := by omega
  obtain ⟨S, T, hS, hT, hsub⟩ := hcov.lt.le
  have hcard_S : quotientPosetRank n G a = S.card := by rw [← hS]; rfl
  have hcard_T : quotientPosetRank n G b = T.card := by rw [← hT]; rfl
  have hcard_gap : S.card + 2 ≤ T.card := by omega
  have hST : S ⊆ T := hsub
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset hST]; omega : 0 < (T \ S).card)
  have hx_mem := Finset.mem_sdiff.mp hx
  let M := insert x S
  have hM_sub_T : M ⊆ T := by
    intro y hy
    simp only [M, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hx_mem.1
    · exact hsub hy
  have hS_sub_M : S ⊆ M := Finset.subset_insert x S
  have hM_card : M.card = S.card + 1 := Finset.card_insert_of_notMem hx_mem.2

  have hle_SM : a ≤ Quotient.mk _ M := ⟨S, M, hS, rfl, hS_sub_M⟩
  have hne_SM : a ≠ Quotient.mk _ M := by
    intro heq
    have := card_eq_of_mk_eq (hS.trans heq)
    omega
  have hlt_SM : a < Quotient.mk _ M := lt_of_le_of_ne hle_SM hne_SM

  have hle_MT : Quotient.mk _ M ≤ b := ⟨M, T, rfl, hT, hM_sub_T⟩
  have hne_MT : Quotient.mk _ M ≠ b := by
    intro heq
    have := card_eq_of_mk_eq (heq.trans hT.symm)
    omega
  have hlt_MT : Quotient.mk _ M < b := lt_of_le_of_ne hle_MT hne_MT
  exact hcov.2 hlt_SM hlt_MT

theorem quotientPosetRank_isMin (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    {a : QuotientPoset n G}
    (hmin : IsMin a) : IsMin (quotientPosetRank n G a) := by
  classical
  suffices h : quotientPosetRank n G a = 0 by
    rw [h]; exact isMin_bot
  induction a using Quotient.inductionOn with
  | _ S =>
    simp only [quotientPosetRank_mk]
    by_contra hne
    have hpos : 0 < S.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hsub : S.erase x ⊆ S := Finset.erase_subset x S
    have hle : Quotient.mk (orbitRel G _) (S.erase x) ≤
               Quotient.mk (orbitRel G _) S :=
      ⟨S.erase x, S, rfl, rfl, hsub⟩
    have hback := hmin hle
    obtain ⟨S', T', hS', hT', hsub'⟩ := hback
    have hcard_S' : S'.card = S.card := card_eq_of_mk_eq hS'
    have hcard_T' : T'.card = (S.erase x).card := card_eq_of_mk_eq hT'
    have := Finset.card_le_card hsub'
    rw [hcard_S', hcard_T', Finset.card_erase_of_mem hx] at this
    omega

end SpernerProperty
