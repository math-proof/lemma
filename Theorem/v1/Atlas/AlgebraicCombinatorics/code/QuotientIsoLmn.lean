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
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

lemma mem_lmnToFinset (p : Lmn m n) (i : Fin m) (j : Fin n) :
    (i, j) ∈ lmnToFinset p ↔ j.val < (p.val i).val := by
  simp [lmnToFinset, Finset.mem_filter]

lemma lmnToFinset_isLeftJustified (p : Lmn m n) :
    WreathOrbits.IsLeftJustified (lmnToFinset p) := by
  intro i j j' hj hlt; rw [mem_lmnToFinset] at hj ⊢; omega

lemma lmnToFinset_rowSize (p : Lmn m n) (i : Fin m) :
    WreathOrbits.rowSize (lmnToFinset p) i = (p.val i).val := by
  unfold WreathOrbits.rowSize
  simp only [lmnToFinset, Finset.filter_filter]
  have h1 : (Finset.univ.filter (fun cell : Fin m × Fin n =>
      (cell.2.val < (p.val cell.1).val) ∧ cell.1 = i)) =
    (Finset.univ.filter (fun cell : Fin m × Fin n =>
      cell.1 = i ∧ cell.2.val < (p.val i).val)) := by
    ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, rfl⟩ => ⟨rfl, h1⟩, fun ⟨rfl, h1⟩ => ⟨h1, rfl⟩⟩
  rw [h1]
  have h2 : (Finset.univ.filter (fun cell : Fin m × Fin n =>
      cell.1 = i ∧ cell.2.val < (p.val i).val)) =
    ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
      j.val < (p.val i).val)).map
      ⟨Prod.mk i, fun a b h => by simpa using h⟩ := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                Function.Embedding.coeFn_mk, Prod.mk.injEq]
    exact ⟨fun ⟨rfl, h1⟩ => ⟨b, h1, rfl, rfl⟩,
           fun ⟨j, hlt, ha, hb⟩ => by cases ha; cases hb; exact ⟨rfl, hlt⟩⟩
  rw [h2, Finset.card_map]
  by_cases hn : (p.val i).val < n
  · have : ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
        j.val < (p.val i).val)) = Finset.Iio (⟨(p.val i).val, hn⟩ : Fin n) := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter, Finset.mem_Iio, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · have hpn : (p.val i).val = n := by omega
    have : ((Finset.univ : Finset (Fin n)).filter (fun j : Fin n =>
        j.val < (p.val i).val)) = Finset.univ := by
      ext ⟨x, hx⟩; simp [Finset.mem_filter]; omega
    rw [this, Finset.card_fin, hpn]

lemma lmnToFinset_isGridYoung (p : Lmn m n) :
    WreathOrbits.IsGridYoung (lmnToFinset p) :=
  ⟨lmnToFinset_isLeftJustified p, fun i j hij => by
    rw [lmnToFinset_rowSize, lmnToFinset_rowSize]; exact p.property hij⟩

end QuotientIsoLmn
