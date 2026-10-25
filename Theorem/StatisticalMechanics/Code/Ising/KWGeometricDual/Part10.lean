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
import Def.StatisticalMechanics.Code.Ising.KWGeometricDual.Part11
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_prod_bond_eq_prod_pow_degree {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (c : ConfigSpace V) (F : Finset E) :
    (∏ e ∈ F, bond c (ends e)) = ∏ v : V, (spin c v) ^ (kwg_degree ends F v) := by
  classical
  induction F using Finset.induction with
  | empty => simp [kwg_degree]
  | @insert e F he ih =>
      rw [Finset.prod_insert he, ih]
      simp_rw [kwg_degree_insert ends F e he, pow_add]
      rw [Finset.prod_mul_distrib, mul_comm]
      congr 1
      induction ends e using Sym2.inductionOn with
      | _ x y =>
          by_cases hxy : x = y
          · subst y
            rw [bond_mk]
            have hs : spin c x * spin c x = 1 := spin_sq c x
            rw [hs]
            symm
            apply Finset.prod_eq_one
            intro v _
            have hi : ¬ kwg_incidentMod2 v s(x, x) := by
              simp [kwg_incidentMod2_mk]
            rw [if_neg hi, pow_zero]
          · rw [bond_mk]
            have hcvt : ∀ v : V,
                (spin c v) ^ (if kwg_incidentMod2 v s(x, y) then 1 else 0) =
                  if v ∈ ({x, y} : Finset V) then spin c v else 1 := by
              intro v
              have hi : kwg_incidentMod2 v s(x, y) ↔ v ∈ ({x, y} : Finset V) := by
                simp only [kwg_incidentMod2_mk, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
                  · exact Or.inl rfl
                  · exact Or.inr rfl
                · rintro (rfl | rfl)
                  · exact Or.inl ⟨rfl, Ne.symm hxy⟩
                  · exact Or.inr ⟨rfl, hxy⟩
              by_cases hv : v ∈ ({x, y} : Finset V)
              · rw [if_pos hv, if_pos (hi.mpr hv), pow_one]
              · rw [if_neg hv, if_neg (fun h => hv (hi.mp h)), pow_zero]
            symm
            calc
              (∏ v : V, (spin c v) ^
                  (if kwg_incidentMod2 v s(x, y) then 1 else 0)) =
                  ∏ v : V, if v ∈ ({x, y} : Finset V) then spin c v else 1 := by
                    apply Finset.prod_congr rfl
                    intro v _
                    exact hcvt v
              _ = spin c x * spin c y := by
                rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pair hxy]


theorem kwg_even_split_card {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (c : V → Bool)
    (hev : kwg_IsEven ends F) :
    Even (F.filter (fun e => kwg_isSplit c (ends e))).card := by
  classical
  have hprod := kwg_prod_bond_eq_prod_pow_degree ends c F
  have hrhs : (∏ v : V, (spin c v) ^ (kwg_degree ends F v)) = (1 : ℝ) := by
    apply Finset.prod_eq_one
    intro v _
    obtain ⟨k, hk⟩ := (kwg_IsEven_iff_degree ends F).mp hev v
    rw [hk, pow_add, ← mul_pow, spin_sq, one_pow]
  have hlhs : (∏ e ∈ F, bond c (ends e)) =
      (-1 : ℝ) ^ (F.filter (fun e => kwg_isSplit c (ends e))).card := by
    calc
      (∏ e ∈ F, bond c (ends e)) =
          ∏ e ∈ F, if kwg_isSplit c (ends e) then (-1 : ℝ) else 1 := by
            apply Finset.prod_congr rfl
            intro e he
            by_cases h : kwg_isSplit c (ends e)
            · rw [if_pos h, (kwg_isSplit_iff_bond_neg c (ends e)).mp h]
            · rw [if_neg h]
              rcases bond_eq_one_or_neg_one c (ends e) with hb | hb
              · exact hb
              · exact (h ((kwg_isSplit_iff_bond_neg c (ends e)).mpr hb)).elim
      _ = (-1 : ℝ) ^ (F.filter (fun e => kwg_isSplit c (ends e))).card := by
        rw [← Finset.prod_filter]
        simp
  rw [hrhs] at hprod
  rw [hlhs] at hprod
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hprod


end Ising
end StatMech
