/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.CorrelationMonotone
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation ConfigSpace

variable {d : ℕ}


theorem plusCorr_shift (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : Multiplicative (Site d)) (x y : Site d) :
    plusCorr d beta (g • x) (g • y) = plusCorr d beta x y := by
  let mu : Measure (ConfigSpace (Site d)) := plusState d beta 0
  have hti := iptp_plusState_isTranslationInvariant (d := d) hbeta
    (by norm_num : (0 : ℝ) ≤ 0)
  unfold plusCorr
  calc
    (∫ omega, spin omega (g • x) * spin omega (g • y)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spin omega (g • x) * spin omega (g • y)
        ∂Measure.map (ConfigSpace.shift g)
          (plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
            rw [hti.map_eq g]
    _ = ∫ omega,
          spin (ConfigSpace.shift g omega) (g • x) *
            spin (ConfigSpace.shift g omega) (g • y)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
      change (∫ omega, spinPairBCF (g • x) (g • y) omega
          ∂Measure.map (ConfigSpace.shift g)
            (plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
        ∫ omega, spinPairBCF (g • x) (g • y)
          (ConfigSpace.shift g omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))
      rw [integral_map (continuous_shift g).measurable.aemeasurable
        (spinPairBCF (g • x) (g • y)).continuous.aestronglyMeasurable]
    _ = _ := by simp_rw [iptp_spin_shift]


theorem gvPlus_pair_nonneg (Lambda : Finset (Site d))
    (beta : ℝ) (hbeta : 0 ≤ beta) (a b : {v // v ∈ Lambda}) :
    0 ≤ ∫ omega, spin omega a.1 * spin omega b.1
      ∂(gvPlusMeasure Lambda beta 0) := by
  rw [gvPlus_pair_eq_vertexField, ← vertexGhost_twoPoint_eq]
  apply twoPointJ_nonneg
  · exact hbeta
  · intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
        cases x <;> cases y <;>
          simp [vertexGhostCoupling, unitEdgeCoupling_nonneg,
            plusBoundaryField_nonneg]


theorem plusCorr_nonneg (beta : ℝ) (hbeta : 0 ≤ beta) (x y : Site d) :
    0 ≤ plusCorr d beta x y := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  obtain ⟨R, hR⟩ := finite_subset_box ({x, y} : Set (Site d))
    (Set.toFinite _)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (plusMeasure_pair_tendsto beta phi hconv x y)
  filter_upwards
    [hphi.tendsto_atTop.eventually (Filter.eventually_ge_atTop R)] with n hn
  have hx : x ∈ boxFinset d (phi n) := by
    rw [mem_boxFinset, mem_box]
    intro i
    exact (hR (by simp) i).trans hn
  have hy : y ∈ boxFinset d (phi n) := by
    rw [mem_boxFinset, mem_box]
    intro i
    exact (hR (by simp) i).trans hn
  rw [← iptp_gvPlusMeasure_eq_plusMeasure]
  exact gvPlus_pair_nonneg (boxFinset d (phi n)) beta hbeta
    ⟨x, hx⟩ ⟨y, hy⟩


theorem plusCorr_le_one (beta : ℝ) (x y : Site d) :
    plusCorr d beta x y ≤ 1 := by
  unfold plusCorr
  have hf : ∀ omega : ConfigSpace (Site d),
      spin omega x * spin omega y ≤ (1 : ℝ) := by
    intro omega
    rcases spin_eq_pm omega x with hx | hx <;>
      rcases spin_eq_pm omega y with hy | hy <;> rw [hx, hy] <;> norm_num
  calc
    (∫ omega, spin omega x * spin omega y
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) ≤
        ∫ _omega, (1 : ℝ)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
      apply integral_mono
      · exact (spinPairBCF x y).integrable _
      · exact integrable_const 1
      · exact hf
    _ = 1 := by simp


theorem plusCorr_eq_origin_translate (beta : ℝ) (hbeta : 0 ≤ beta)
    (x y : Site d) :
    plusCorr d beta x y =
      plusCorr d beta (Percolation.origin d) (y - x) := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have h := plusCorr_shift beta hbeta g (Percolation.origin d) (y - x)
  have hg0 : g • Percolation.origin d = x := by
    ext i
    simp [g, Percolation.origin]
  have hgy : g • (y - x) = y := by
    ext i
    simp [g]
  rw [hg0, hgy] at h
  exact h


end Sharpness
end StatMech
