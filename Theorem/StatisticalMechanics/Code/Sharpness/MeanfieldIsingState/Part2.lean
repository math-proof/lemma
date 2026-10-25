/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFull.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState
open MeasureTheory Real Set Filter Topology
open scoped BigOperators


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


theorem sctFieldToZero_pos (n : ℕ) : 0 < sctFieldToZero n := by
  unfold sctFieldToZero
  positivity

theorem sctFieldToZero_antitone : Antitone sctFieldToZero := by
  intro n m hnm
  unfold sctFieldToZero
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hnm 1


theorem sctInfiniteFieldMag_tendsto_zeroPlus (d : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto (fun n => sctInfiniteFieldMag d beta (sctFieldToZero n))
      atTop (nhds (sctZeroPlusMag d beta)) := by
  apply tendsto_atTop_ciInf
  · intro n m hnm
    have hn0 : 0 ≤ sctFieldToZero n := (sctFieldToZero_pos n).le
    have hm0 : 0 ≤ sctFieldToZero m := (sctFieldToZero_pos m).le
    exact sctInfiniteFieldMag_monotone_field d beta hbeta hm0 hn0
      (sctFieldToZero_antitone hnm)
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sctInfiniteFieldMag_nonneg d beta (sctFieldToZero n)
      hbeta (sctFieldToZero_pos n).le


theorem sct_integral_freeState_tendsto_zeroPlus (d : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun n => ∫ omega, spin omega (Percolation.origin d)
        ∂(freeState d beta (sctFieldToZero n) :
          Measure (ConfigSpace (Site d))))
      atTop (nhds (sctZeroPlusMag d beta)) := by
  have hlim := sctInfiniteFieldMag_tendsto_zeroPlus d beta hbeta
  simpa only [sct_integral_freeState_eq_infiniteFieldMag d beta _ hbeta
    (sctFieldToZero_pos _).le] using hlim


theorem sctZeroPlus_meanfield_lower_bound_of_deriv_tendsto
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d)
    (hdiff : ∀ k : ℕ, ∀ gamma ∈ Ici (tildeBetaCIsing d),
      DifferentiableAt ℝ
        (fun b => (sctInfiniteFieldMag d b (sctFieldToZero k)) ^ 2) gamma)
    (hderiv : ∀ k : ℕ, ∀ gamma ∈ Ioi (tildeBetaCIsing d),
      Tendsto
        (fun n : ℕ => deriv
          (fun b => (sctOriginMag d b (sctFieldToZero k) (n + 1)) ^ 2) gamma)
        atTop
        (nhds (deriv
          (fun b => (sctInfiniteFieldMag d b (sctFieldToZero k)) ^ 2) gamma)))
    {beta : ℝ} (hbeta : tildeBetaCIsing d ≤ beta) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      sctZeroPlusMag d beta := by
  have hcrit0 : 0 ≤ tildeBetaCIsing d := hcrit.le
  have hbounds : ∀ k : ℕ,
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        sctInfiniteFieldMag d beta (sctFieldToZero k) := by
    intro k
    apply meanfield_lower_bound_of_initial_nonneg
      (tildeBetaCIsing d) hcrit
      (fun b => sctInfiniteFieldMag d b (sctFieldToZero k))
      (hdiff k)
    · intro gamma hgamma
      exact sct_infiniteField_meanfield_inequality_of_deriv_tendsto
        d gamma (sctFieldToZero k) hbdd hgamma
        (sctFieldToZero_pos k) (hderiv k gamma hgamma)
    · intro gamma hgamma
      have hgamma0 : 0 ≤ gamma := hcrit0.trans (mem_Ici.mp hgamma)
      exact sctInfiniteFieldMag_nonneg d gamma (sctFieldToZero k)
        hgamma0 (sctFieldToZero_pos k).le
    · exact hbeta
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (sctInfiniteFieldMag_tendsto_zeroPlus d beta
      (hcrit0.trans hbeta))
    (Filter.Eventually.of_forall hbounds)

end Sharpness
end StatMech
