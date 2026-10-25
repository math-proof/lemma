/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.BaseCase
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind
import Def.StatisticalMechanics.Code.Onsager.WalkCrossing.Part3


namespace StatMech.Onsager.WalkCrossing

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager.NoDoubleWind

variable {n : ℕ} [NeZero n]


theorem onEdge_horiz_endpoint (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isHorizEdge (d k)) (p : ℤ × ℤ) (hp : onEdge d k p) :
    p = pos d k ∨ p = pos d (k + 1) := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hp
  have hyc := horiz_y_const d hclosed k hk
  have hxs := horiz_x_step d hclosed k hk
  have hpy : p.2 = (pos d k).2 := by omega
  have hpx : p.1 = (pos d k).1 ∨ p.1 = (pos d (k + 1)).1 := by
    rcases hxs with h | h <;> rw [h] at hx1 hx2 ⊢ <;> omega
  rcases hpx with h | h
  · exact Or.inl (Prod.ext h hpy)
  · exact Or.inr (Prod.ext h (by rw [hpy]; exact hyc.symm))


theorem onEdge_vert_endpoint (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k : Fin n) (hk : isVertEdge (d k)) (p : ℤ × ℤ) (hp : onEdge d k p) :
    p = pos d k ∨ p = pos d (k + 1) := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hp
  have hxc := vert_x_const d hclosed k hk
  have hys := vert_y_step d hclosed k hk
  have hpx : p.1 = (pos d k).1 := by omega
  have hpy : p.2 = (pos d k).2 ∨ p.2 = (pos d (k + 1)).2 := by
    rcases hys with h | h <;> rw [h] at hy1 hy2 ⊢ <;> omega
  rcases hpy with h | h
  · exact Or.inl (Prod.ext hpx h)
  · exact Or.inr (Prod.ext (by rw [hpx]; exact hxc.symm) h)


theorem horiz_vert_cross_shared_vertex (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k j : Fin n) (hk : isHorizEdge (d k)) (hj : isVertEdge (d j)) (p : ℤ × ℤ)
    (hpk : onEdge d k p) (hpj : onEdge d j p) :
    (p = pos d k ∨ p = pos d (k + 1)) ∧ (p = pos d j ∨ p = pos d (j + 1)) :=
  ⟨onEdge_horiz_endpoint d hclosed k hk p hpk, onEdge_vert_endpoint d hclosed j hj p hpj⟩


theorem edges_cross_not_injective (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (k j : Fin n) (hk : isHorizEdge (d k)) (hj : isVertEdge (d j))
    (hne1 : k ≠ j) (hne2 : k + 1 ≠ j) (hne3 : k ≠ j + 1) (hne4 : k + 1 ≠ j + 1)
    (p : ℤ × ℤ) (hpk : onEdge d k p) (hpj : onEdge d j p) :
    ¬ Function.Injective (pos d) := by
  intro hinj
  rcases onEdge_horiz_endpoint d hclosed k hk p hpk with hak | hak <;>
    rcases onEdge_vert_endpoint d hclosed j hj p hpj with hbj | hbj
  · exact hne1 (hinj (hak.symm.trans hbj))
  · exact hne3 (hinj (hak.symm.trans hbj))
  · exact hne2 (hinj (hak.symm.trans hbj))
  · exact hne4 (hinj (hak.symm.trans hbj))


end StatMech.Onsager.WalkCrossing
