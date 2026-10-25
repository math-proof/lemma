/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part2
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusEdgeOfCode_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusEdgeOfCode L) := by
  have htwo : (2 : ZMod L) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod L) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      have := (Fact.out : 2 < L)
      omega
    simpa using h
  have hone : (1 : ZMod L) ≠ 0 := by
    intro h
    apply htwo
    linear_combination 2 * h
  rintro ⟨⟨x, y⟩, o⟩ ⟨⟨x', y'⟩, o'⟩ h
  cases o <;> cases o'
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusHorizontalEdge_val,
      Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨hxy, _⟩ | ⟨hxx, hyy⟩
    · rcases hxy with ⟨rfl, rfl⟩
      rfl
    · exfalso
      apply htwo
      linear_combination hyy.1 - hxx.1
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusHorizontalEdge_val,
      torusVerticalEdge_val, Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with h | h
    · exfalso
      apply hone
      linear_combination h.2.1 - h.1.1
    · exfalso
      apply hone
      linear_combination h.2.1 - h.1.1
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusHorizontalEdge_val,
      torusVerticalEdge_val, Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with h | h
    · exfalso
      apply hone
      linear_combination h.2.2 - h.1.2
    · exfalso
      apply hone
      linear_combination h.2.2 - h.1.2
  · simp only [torusEdgeOfCode, Subtype.ext_iff, torusVerticalEdge_val,
      Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨hxy, _⟩ | ⟨hxx, hyy⟩
    · rcases hxy with ⟨rfl, rfl⟩
      rfl
    · exfalso
      apply htwo
      linear_combination hyy.2 - hxx.2

theorem torusEdgeOfCode_surjective (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (torusEdgeOfCode L) := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, onsTorusGraph] at he
      rcases he with (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
      · refine ⟨⟨v, .vertical⟩, ?_⟩
        apply Subtype.ext
        change s((v.1, v.2), (v.1, v.2 + 1)) = s(u, v)
        rw [Sym2.eq_iff]
        right
        exact ⟨rfl, Prod.ext h0.symm h1.symm⟩
      · refine ⟨⟨u, .vertical⟩, ?_⟩
        apply Subtype.ext
        change s((u.1, u.2), (u.1, u.2 + 1)) = s(u, v)
        rw [Sym2.eq_iff]
        left
        exact ⟨rfl, Prod.ext h0 (by linear_combination h1)⟩
      · refine ⟨⟨v, .horizontal⟩, ?_⟩
        apply Subtype.ext
        change s((v.1, v.2), (v.1 + 1, v.2)) = s(u, v)
        rw [Sym2.eq_iff]
        right
        exact ⟨rfl, Prod.ext h0.symm h1.symm⟩
      · refine ⟨⟨u, .horizontal⟩, ?_⟩
        apply Subtype.ext
        change s((u.1, u.2), (u.1 + 1, u.2)) = s(u, v)
        rw [Sym2.eq_iff]
        left
        exact ⟨rfl, Prod.ext (by linear_combination h0) h1⟩


end StatMech.BeffaraDC
