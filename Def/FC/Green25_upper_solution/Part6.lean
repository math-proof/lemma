/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution.Part5
open Asymptotics Filter Finset


namespace Green25

def shiftPartition25 {s : Finset ℕ} (a : ℕ) (P : Finpartition s) :
    Finpartition (shift25 a s) where
  parts := P.parts.image (shift25 a)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_image]
    rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hAB
    rw [Function.onFun, id_eq, Finset.disjoint_left]
    intro z hzp hzq
    change z ∈ shift25 a p at hzp
    change z ∈ shift25 a q at hzq
    rw [shift25, Finset.mem_image] at hzp hzq
    obtain ⟨x, hx, rfl⟩ := hzp
    obtain ⟨y, hy, hxy⟩ := hzq
    have hxy' : x = y := by omega
    subst y
    have hd := P.disjoint hp hq (fun h => hAB (congrArg (shift25 a) h))
    change Disjoint p q at hd
    rw [Finset.disjoint_left] at hd
    exact hd hx hy
  sup_parts := by
    ext x
    simp only [Finset.mem_sup, Finset.mem_image]
    constructor
    · rintro ⟨u, ⟨p, hp, hpu⟩, hu⟩
      subst u
      change x ∈ shift25 a p at hu
      rw [shift25, Finset.mem_image] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      rw [shift25, Finset.mem_image]
      refine ⟨y, ?_, rfl⟩
      rw [← P.sup_parts, Finset.mem_sup]
      exact ⟨p, hp, hy⟩
    · change x ∈ s.image (a + ·) → _
      rw [Finset.mem_image]
      rintro ⟨y, hy, rfl⟩
      rw [← P.sup_parts, Finset.mem_sup] at hy
      obtain ⟨p, hp, hyp⟩ := hy
      refine ⟨shift25 a p, ⟨p, hp, rfl⟩, ?_⟩
      change a + y ∈ shift25 a p
      exact Finset.mem_image.mpr ⟨y, hyp, rfl⟩
  bot_notMem := by
    rw [Finset.mem_image]
    rintro ⟨p, hp, hzero⟩
    have hpzero : p = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      have hm : a + x ∈ shift25 a p := by
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rw [hzero] at hm
      exact (Finset.notMem_empty _ hm).elim
    subst p
    exact P.bot_notMem hp

end Green25
