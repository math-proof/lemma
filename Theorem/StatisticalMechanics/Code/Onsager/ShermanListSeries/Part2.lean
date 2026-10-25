/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4Return.Part3
import Def.StatisticalMechanics.Code.Onsager.ShermanListSeries


namespace StatMech.Onsager

open BigOperators

theorem list_norm_prod_nonneg {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) : 0 ≤ (l.map fun a => ‖wt a‖).prod := by
  apply List.prod_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact norm_nonneg _

theorem norm_listSeriesTerm_le {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) :
    ‖ons_listSeriesTerm wt l‖ ≤ (l.map fun a => ‖wt a‖).prod := by
  unfold ons_listSeriesTerm
  split_ifs with h
  · subst l
    simp
  · calc
      ‖(l.map wt).prod / (l.length : ℂ)‖ =
          ‖(l.map wt).prod‖ / ‖(l.length : ℂ)‖ := norm_div _ _
      _ ≤ (l.map fun a => ‖wt a‖).prod / ‖(l.length : ℂ)‖ := by
        have hn := List.norm_prod_le (l.map wt)
        simpa [List.map_map, Function.comp_def] using
          div_le_div_of_nonneg_right hn (norm_nonneg (l.length : ℂ))
      _ ≤ (l.map fun a => ‖wt a‖).prod := by
        apply div_le_self
        · exact list_norm_prod_nonneg wt l
        · rw [norm_natCast]
          exact_mod_cast (List.length_pos_iff.mpr h)

theorem summable_listNormProd {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    Summable (fun l : List alpha => (l.map fun a => ‖wt a‖).prod) := by
  let equiv : (Sigma fun n : ℕ => Fin n → alpha) ≃ List alpha :=
    (List.equivSigmaTuple : List alpha ≃ Sigma fun n : ℕ => Fin n → alpha).symm
  apply equiv.summable_iff.mp
  rw [summable_sigma_of_nonneg (fun x => by
    change 0 ≤ (List.map (fun a => ‖wt a‖) (equiv x)).prod
    exact list_norm_prod_nonneg wt (equiv x))]
  constructor
  · intro k
    simpa [equiv, List.equivSigmaTuple_symm_apply, List.map_ofFn, List.prod_ofFn,
      Function.comp_def] using ons_summable_tupleProd (fun a => ‖wt a‖) hwt k
  ·
    have hnonneg : 0 ≤ ∑' a : alpha, ‖wt a‖ :=
      tsum_nonneg (fun a : alpha => norm_nonneg (wt a))
    have hpow := summable_geometric_of_norm_lt_one
      (K := ℝ) (by
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hsmall)
    convert hpow using 1
    funext k
    rw [← ons_tsum_tupleProd_eq_pow (fun a => ‖wt a‖) hwt k]
    apply tsum_congr
    intro p
    simp [equiv, List.equivSigmaTuple_symm_apply, List.map_ofFn, List.prod_ofFn,
      Function.comp_def]


theorem ons_summable_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    Summable (ons_listSeriesTerm wt) :=
  Summable.of_norm_bounded (summable_listNormProd wt hwt hsmall)
    (norm_listSeriesTerm_le wt)


theorem ons_tsum_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (hwt : Summable fun a => ‖wt a‖) (hsmall : ∑' a, ‖wt a‖ < 1) :
    (∑' l : List alpha, ons_listSeriesTerm wt l) =
      ∑' k : ℕ, (∑' a, wt a) ^ (k + 1) / (k + 1) := by
  have hwt' : Summable wt := Summable.of_norm hwt
  have hall := ons_summable_listSeriesTerm wt hwt hsmall
  let equiv : (Sigma fun n : ℕ => Fin n → alpha) ≃ List alpha :=
    (List.equivSigmaTuple : List alpha ≃ Sigma fun n : ℕ => Fin n → alpha).symm
  rw [← equiv.tsum_eq]
  have hsigma : Summable (ons_listSeriesTerm wt ∘ equiv) :=
    equiv.summable_iff.mpr hall
  change (∑' c, (ons_listSeriesTerm wt ∘ equiv) c) = _
  rw [hsigma.tsum_sigma]
  have houter := hsigma.sigma
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 houter)]
  have hzero : (∑' c : Fin 0 → alpha,
      (ons_listSeriesTerm wt ∘ equiv) ⟨0, c⟩) = 0 := by
    letI : Finite (Fin 0 → alpha) := Finite.of_subsingleton
    letI : Fintype (Fin 0 → alpha) := Fintype.ofFinite _
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro c _
    simp [equiv, ons_listSeriesTerm]
  rw [hzero, zero_add]
  apply tsum_congr
  intro k
  simp only [equiv, List.equivSigmaTuple_symm_apply, Function.comp_apply]
  have hne (p : Fin (k + 1) → alpha) : List.ofFn p ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  simp_rw [ons_listSeriesTerm, dif_neg (hne _)]
  simp only [List.map_ofFn, List.prod_ofFn, List.length_ofFn, Function.comp_def]
  rw [tsum_div_const]
  rw [ons_tsum_tupleProd_eq_pow wt hwt' (k + 1)]
  push_cast
  ring

end StatMech.Onsager
