/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part10
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_IsEven_iff_degree {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) :
    kwg_IsEven ends F ↔ ∀ v, Even (kwg_degree ends F v) := by
  rfl


theorem kwg_IsEven_sdiff {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) {F S : Finset E} (hSF : S ⊆ F)
    (hF : kwg_IsEven ends F) (hS : kwg_IsEven ends S) :
    kwg_IsEven ends (F \ S) := by
  classical
  intro v
  let p : E → Prop := fun e => kwg_incidentMod2 v (ends e)
  have hfilter :
      (F \ S).filter p = F.filter p \ S.filter p := by
    ext e
    by_cases hp : p e <;> simp [hp]
  rw [hfilter, Finset.card_sdiff]
  have hinter : S.filter p ∩ F.filter p = S.filter p :=
    Finset.inter_eq_left.mpr (Finset.filter_subset_filter p hSF)
  rw [hinter]
  have hle : (S.filter p).card ≤ (F.filter p).card :=
    Finset.card_le_card (Finset.filter_subset_filter p hSF)
  rw [Nat.even_sub hle]
  exact ⟨fun _ => hS v, fun _ => hF v⟩

theorem kwg_degree_insert {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) (e : E) (he : e ∉ F) (v : V) :
    kwg_degree ends (insert e F) v = kwg_degree ends F v +
      (if kwg_incidentMod2 v (ends e) then 1 else 0) := by
  classical
  unfold kwg_degree
  rw [Finset.filter_insert]
  by_cases hv : kwg_incidentMod2 v (ends e)
  · rw [if_pos hv, Finset.card_insert_of_notMem (by simp [he]), if_pos hv]
  · rw [if_neg hv, if_neg hv, add_zero]


end Ising
end StatMech
