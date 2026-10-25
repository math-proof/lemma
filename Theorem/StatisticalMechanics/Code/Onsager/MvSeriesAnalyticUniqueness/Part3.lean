/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleAffine
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval.Part2
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Def.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness.Part2


namespace StatMech.Onsager

open BigOperators

open Filter

theorem ons_degreeFiberPolynomial_eval
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : MvPowerSeries E ℂ) (weight : E → ℂ) (n : ℕ) :
    MvPolynomial.eval weight (ons_degreeFiberPolynomial series n) =
      ons_degreeFiberCoeff series weight n := by
  let T := (Finsupp.finite_of_degree_le (σ := E) n).toFinset.filter
    (fun m ↦ Finsupp.degree m = n)
  let fiberFinite : Set.Finite
      {m : E →₀ ℕ | Finsupp.degree m = n} :=
    (Finsupp.finite_of_degree_le (σ := E) n).subset (by
      intro m hm
      show Finsupp.degree m ≤ n
      rw [hm])
  letI : Fintype {m : E →₀ ℕ // Finsupp.degree m = n} :=
    fiberFinite.fintype
  unfold ons_degreeFiberPolynomial ons_degreeFiberCoeff
  rw [MvPolynomial.eval_sum]
  simp only [MvPolynomial.eval_monomial]
  change (∑ m ∈ T, MvPowerSeries.coeff m series *
      ons_mvMonomialValue weight m) = _
  rw [tsum_fintype]
  exact Finset.sum_subtype T (by
    intro m
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨by omega, h⟩)
    (fun m ↦ MvPowerSeries.coeff m series *
      ons_mvMonomialValue weight m)

theorem ons_coeff_eq_zero_of_degreeFiberCoeff
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : MvPowerSeries E ℂ) (m : E →₀ ℕ)
    (hzero : ∀ weight : E → ℂ,
      ons_degreeFiberCoeff series weight (Finsupp.degree m) = 0) :
    MvPowerSeries.coeff m series = 0 := by
  let n := Finsupp.degree m
  let T := (Finsupp.finite_of_degree_le (σ := E) n).toFinset.filter
    (fun d ↦ Finsupp.degree d = n)
  let P := ons_degreeFiberPolynomial series n
  have hPeval : ∀ weight : E → ℂ, MvPolynomial.eval weight P = 0 := by
    intro weight
    rw [show P = ons_degreeFiberPolynomial series n from rfl,
      ons_degreeFiberPolynomial_eval]
    exact hzero weight
  have hP : P = 0 := MvPolynomial.funext hPeval
  have hmT : m ∈ T := by
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    exact ⟨le_rfl, rfl⟩
  have hcoeff : MvPolynomial.coeff m P =
      MvPowerSeries.coeff m series := by
    change MvPolynomial.coeff m
        (∑ d ∈ T,
          MvPolynomial.monomial d (MvPowerSeries.coeff d series)) = _
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single m]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro d hd hdm
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact hdm
    · exact fun hnot ↦ (hnot hmT).elim
  rw [hP] at hcoeff
  simpa using hcoeff.symm

end StatMech.Onsager
