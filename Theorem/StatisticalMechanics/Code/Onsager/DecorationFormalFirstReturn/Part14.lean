/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part14


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalFirstReturnTrunc_coeff
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (N : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d N) =
      ∑ atom : ons_DecFirstReturnAtomBounded L d N,
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom
        else 0 := by
  classical
  unfold ons_decFormalFirstReturnTrunc
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro atom hatom
  rw [MvPowerSeries.coeff_monomial]
  by_cases h : ons_decBoundedAtomExponent atom = m
  · subst m
    simp
  · simp [h, Ne.symm h]

theorem ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (N : ℕ)
    (hdegree : ons_finsuppTotalDegree m ≤ N) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d) =
      MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d N) := by
  rw [ons_decFormalFirstReturnTrunc_coeff]
  exact ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms_of_degree_le
    L a b d m N hdegree

theorem ons_finsuppTotalDegree_mono
    {E : Type*} [DecidableEq E] {m n : E →₀ ℕ} (h : m ≤ n) :
    ons_finsuppTotalDegree m ≤ ons_finsuppTotalDegree n := by
  unfold ons_finsuppTotalDegree
  exact Finsupp.sum_le_sum_index h
    (fun _ _ ↦ monotone_id) (fun _ _ ↦ rfl)

theorem ons_decFormalFirstReturn_coeff_pow_eq_trunc
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) =
      MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d
          (ons_finsuppTotalDegree m) ^ k) := by
  classical
  rw [MvPowerSeries.coeff_pow, MvPowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro exponents hexponents
  apply Finset.prod_congr rfl
  intro i hi
  apply ons_decFormalFirstReturn_coeff_eq_trunc_of_degree_le
  apply ons_finsuppTotalDegree_mono
  have hsum := (Finset.mem_finsuppAntidiag.mp hexponents).1
  rw [← hsum]
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) hi

theorem ons_decFormalFirstReturnTrunc_coeff_pow
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (N k : ℕ) (m : ons_DecEdge L →₀ ℕ) :
    MvPowerSeries.coeff m
        (ons_decFormalFirstReturnTrunc L a b d N ^ k) =
      ∑ atoms : Fin k → ons_DecFirstReturnAtomBounded L d N,
        if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then
          ∏ i, ons_decBoundedAtomWeight L a b (atoms i)
        else 0 := by
  classical
  unfold ons_decFormalFirstReturnTrunc
  rw [Fintype.sum_pow, map_sum]
  apply Finset.sum_congr rfl
  intro atoms hatoms
  have hprod :
      (∏ i,
        MvPowerSeries.monomial (ons_decBoundedAtomExponent (atoms i))
          (ons_decBoundedAtomWeight L a b (atoms i))) =
        MvPowerSeries.monomial
          (∑ i, ons_decBoundedAtomExponent (atoms i))
          (∏ i, ons_decBoundedAtomWeight L a b (atoms i)) := by
    simpa using MvPowerSeries.prod_monomial
      (fun i : Fin k ↦ ons_decBoundedAtomExponent (atoms i))
      (fun i : Fin k ↦ ons_decBoundedAtomWeight L a b (atoms i))
      (Finset.univ : Finset (Fin k))
  rw [hprod, MvPowerSeries.coeff_monomial]
  by_cases h : (∑ i, ons_decBoundedAtomExponent (atoms i)) = m
  · subst m
    simp
  · simp [h, Ne.symm h]

theorem ons_decFormalFirstReturn_coeff_pow_eq_boundedTupleSum
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) (k : ℕ) :
    MvPowerSeries.coeff m (ons_decFormalFirstReturn L a b d ^ k) =
      ∑ atoms : Fin k → ons_DecFirstReturnAtomBounded L d
          (ons_finsuppTotalDegree m),
        if (∑ i, ons_decBoundedAtomExponent (atoms i)) = m then
          ∏ i, ons_decBoundedAtomWeight L a b (atoms i)
        else 0 := by
  rw [ons_decFormalFirstReturn_coeff_pow_eq_trunc,
    ons_decFormalFirstReturnTrunc_coeff_pow]

end StatMech.Onsager
