/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem criticalCenteredSpinUpGap_nonneg (r : Nat) :
    0 <= criticalCenteredSpinUpGap r := by
  let c : Fin (2 * r + 1) := ⟨r, by omega⟩
  have hle := isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
    r r c c
      (by change r <= r; exact le_rfl)
      (by change r + r <= 2 * r; omega)
      (by change r <= r; exact le_rfl)
      (by change r + r <= 2 * r; omega)
  exact (oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
    isingBetaC_three_pos.le r _).trans hle

theorem oddPrismCriticalSurfaceSpinSquareAverage_le
    (n r : Nat) :
    oddPrismCriticalSurfaceSpinSquareAverage n <=
      criticalCenteredSpinUpGap r ^ 2 +
        (4 * r : Real) / (((2 * n + 1 : Nat) : Real)) := by
  classical
  let L := 2 * n + 1
  let U : Finset (Fin (2 * n + 1) × Fin (2 * n + 1)) := Finset.univ
  let good := U.filter (oddPrismSurfaceInterior n r)
  let bad := oddPrismSurfaceNonInterior n r
  let f : Fin (2 * n + 1) × Fin (2 * n + 1) -> Real := fun q =>
    oddPrismPlusSpinMean (Ising.betaC 3) n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1 ^ 2
  unfold oddPrismCriticalSurfaceSpinSquareAverage
  change Finset.univ.sum f / (((2 * n + 1 : Nat) : Real) ^ 2) <=
    criticalCenteredSpinUpGap r ^ 2 +
      (4 * r : Real) / ((2 * n + 1 : Nat) : Real)
  have hsplit : good.sum f + bad.sum f = U.sum f := by
    simpa [good, bad, oddPrismSurfaceNonInterior] using
      (Finset.sum_filter_add_sum_filter_not U
        (oddPrismSurfaceInterior n r) f)
  have hgoodTerm : forall q, q ∈ good ->
      f q <= criticalCenteredSpinUpGap r ^ 2 := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    have hle := isingCritical_oddPrismPlusSurfaceSpinMean_le_centeredGap
      n r q.1 q.2 hq'.1 hq'.2.1 hq'.2.2.1 hq'.2.2.2
    have hm0 := oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
      isingBetaC_three_pos.le n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
    exact (sq_le_sq₀ hm0 (criticalCenteredSpinUpGap_nonneg r)).2 hle
  have hgood : good.sum f <=
      (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 := by
    calc
      good.sum f <= good.card * criticalCenteredSpinUpGap r ^ 2 := by
        simpa using Finset.sum_le_card_nsmul good f
          (criticalCenteredSpinUpGap r ^ 2) hgoodTerm
      _ <= (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 := by
        gcongr
        norm_cast
        simpa [U, L, pow_two] using Finset.card_filter_le U
          (oddPrismSurfaceInterior n r)
  have hbadTerm : forall q, q ∈ bad -> f q <= 1 := by
    intro q _
    have hm0 := oddPrismPlusSpinMean_nonneg (Ising.betaC 3)
      isingBetaC_three_pos.le n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
    have hm1 := oddPrismPlusSpinMean_le_one (Ising.betaC 3) n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
    dsimp [f]
    nlinarith
  have hbadCard : bad.card <= 4 * r * L := by
    exact (Finset.card_le_card
      (oddPrismSurface_not_interior_subset_boundary n r)).trans
        (by simpa [bad, L] using oddPrismSurfaceBoundaryPairs_card_le n r)
  have hbad : bad.sum f <= (4 * r * L : Nat) := by
    calc
      bad.sum f <= bad.card * (1 : Real) := by
        simpa using Finset.sum_le_card_nsmul bad f (1 : Real) hbadTerm
      _ <= (4 * r * L : Nat) := by
        norm_num
        exact_mod_cast hbadCard
  have hsum : U.sum f <=
      (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 +
        (4 * r * L : Nat) := by
    rw [<- hsplit]
    gcongr
  have hL : (0 : Real) < L := by positivity
  rw [div_le_iff₀ (sq_pos_of_pos hL)]
  calc
    U.sum f <= (L : Real) ^ 2 * criticalCenteredSpinUpGap r ^ 2 +
        (4 * r * L : Nat) := hsum
    _ = (criticalCenteredSpinUpGap r ^ 2 +
          (4 * r : Real) / L) * (L : Real) ^ 2 := by
      push_cast
      field_simp


theorem oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero :
    Tendsto oddPrismCriticalSurfaceSpinSquareAverage atTop (nhds 0) := by
  let r : Nat -> Nat := fun n => Nat.sqrt n
  let upper : Nat -> Real := fun n =>
    criticalCenteredSpinUpGap (r n) ^ 2 +
      (4 : Real) * ((r n : Nat) : Real) / (2 * n + 1)
  have hgap : Tendsto (fun n => criticalCenteredSpinUpGap (r n))
      atTop (nhds 0) :=
    (isingCritical_centeredBox_spinUp_extremalGap_tendsto_zero
      (origin 3)).comp StatMech.FK.ocs_sqrt_tendsto_atTop
  have hboundary : Tendsto
      (fun n => (4 : Real) * ((r n : Nat) : Real) / (2 * n + 1))
      atTop (nhds 0) := by
    have hratio := StatMech.FK.ocs_sqrt_div_to_zero
    have hdiv : Tendsto (fun n => ((r n : Nat) : Real) / (2 * n + 1))
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun n => by positivity
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have hpos : (0 : Real) < n := by exact_mod_cast hn
        have hdenpos : (0 : Real) < 2 * n + 1 := by positivity
        dsimp [r]
        have hsqrt : (0 : Real) <= Nat.sqrt n := by positivity
        exact div_le_div_of_nonneg_left hsqrt hpos (by nlinarith)
      · simpa [r] using hratio
    simpa [mul_div_assoc] using tendsto_const_nhds.mul hdiv
  have hu : Tendsto upper atTop (nhds 0) := by
    simpa [upper] using (hgap.pow 2).add hboundary
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      unfold oddPrismCriticalSurfaceSpinSquareAverage
      positivity
  · exact Filter.Eventually.of_forall fun n => by
      have h := oddPrismCriticalSurfaceSpinSquareAverage_le n (r n)
      simpa [Nat.cast_mul] using h
  · exact hu


end
end StatMech.FrontierA
