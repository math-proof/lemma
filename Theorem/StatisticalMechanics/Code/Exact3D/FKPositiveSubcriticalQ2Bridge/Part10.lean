/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part10
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer_shift
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) :
    Monotone fun k : ℕ =>
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (n + k) n := by
  simpa [freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume, FK.boxConnEvent] using
    (FK.fkFreeLimit_monotone (d := 3) n
      (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)
      (S := FK.connEvent (FK.boxGraph 3 n)
        (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n))
      (FK.connEvent_isIncreasing (FK.boxGraph 3 n)
        (ising3DOriginBoxVertex n) (ising3DXAxisBoxVertex n)))


theorem freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer
    (β : ℝ) (hβpos : 0 < β) {n M₁ M₂ : ℕ}
    (hM₁ : n ≤ M₁) (hM : M₁ ≤ M₂) :
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M₁ n ≤
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M₂ n := by
  obtain ⟨k₁, rfl⟩ := Nat.exists_eq_add_of_le hM₁
  obtain ⟨k₂, hk₂⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right n k₁) hM)
  have hk : k₁ ≤ k₂ := by omega
  rw [hk₂]
  exact freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer_shift
    β hβpos n hk


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hcompareHi⟩
  refine
    ⟨fun n : ℕ => C * (n : ℝ) ^ k,
      PositiveSubexponentialPrefactor.const_mul hC
        (PositiveSubexponentialPrefactor.natCast_pow k), ?_⟩
  exact hcompareHi


theorem
    freeQ2BoundaryProfileFiniteVolumeComparisonToXAxis_of_profileFiniteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hcompareHi⟩
  refine
    ⟨fun n : ℕ => C * (n : ℝ) ^ k,
      PositiveSubexponentialPrefactor.const_mul hC
        (PositiveSubexponentialPrefactor.natCast_pow k), ?_⟩
  exact hcompareHi


theorem
    freeQ2BoundaryProfileScaledFiniteVolumePolynomial_of_finiteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hcompareHi⟩
  classical
  let good : ℕ → Prop := fun n =>
    ∃ M, n ≤ M ∧
      freeQ2BoundaryProfileOfBeta β hβpos n ≤
        C * (n : ℝ) ^ k *
          freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n
  let outerScale : ℕ → ℕ := fun n =>
    if h : good n then Classical.choose h else n
  refine ⟨outerScale, C, k, hC, ?_, ?_⟩
  · filter_upwards [hcompareHi] with n hcompare_n
    have hgood : good n := by
      have hev :
          ∀ᶠ M in atTop,
            n ≤ M ∧
              freeQ2BoundaryProfileOfBeta β hβpos n ≤
                C * (n : ℝ) ^ k *
                  freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
                    β hβpos M n :=
        (eventually_ge_atTop n).and hcompare_n
      exact hev.exists
    simpa [outerScale, hgood] using (Classical.choose_spec hgood).1
  · filter_upwards [hcompareHi] with n hcompare_n
    have hgood : good n := by
      have hev :
          ∀ᶠ M in atTop,
            n ≤ M ∧
              freeQ2BoundaryProfileOfBeta β hβpos n ≤
                C * (n : ℝ) ^ k *
                  freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume
                    β hβpos M n :=
        (eventually_ge_atTop n).and hcompare_n
      exact hev.exists
    simpa [outerScale, hgood] using (Classical.choose_spec hgood).2


theorem
    freeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxis_of_scaledFiniteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with
    ⟨outerScale, C, k, hC, hscaleHi, hcompareHi⟩
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [hscaleHi, hcompareHi] with n hscale_n hcompare_n
  filter_upwards [eventually_ge_atTop (outerScale n)] with M hM
  have hmono :
      freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (outerScale n) n ≤
        freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n :=
    freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume_mono_outer
      β hβpos hscale_n hM
  have hcoeff_nonneg : 0 ≤ C * (n : ℝ) ^ k :=
    mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg n) k)
  exact le_trans hcompare_n
    (mul_le_mul_of_nonneg_left hmono hcoeff_nonneg)


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨Aratio, hAratio, hcompareHi⟩
  refine ⟨Aratio, hAratio, ?_⟩
  filter_upwards [hcompareHi] with n hcompare_n
  have hlim :
      Tendsto
        (fun M : ℕ =>
          Aratio n *
            freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n)
        atTop
        (nhds
          (Aratio n *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n)) := by
    simpa using
      (tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos n).const_mul
        (Aratio n)
  exact ge_of_tendsto hlim hcompare_n


theorem
    freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileFiniteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical := by
  intro β hβpos hβc
  rcases hcompare β hβpos hβc with ⟨C, k, hC, hcompareHi⟩
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [hcompareHi] with n hcompare_n
  have hlim :
      Tendsto
        (fun M : ℕ =>
          C * (n : ℝ) ^ k *
            freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos M n)
        atTop
        (nhds
          (C * (n : ℝ) ^ k *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n)) := by
    simpa using
      (tendsto_freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos n).const_mul
        (C * (n : ℝ) ^ k)
  exact ge_of_tendsto hlim hcompare_n


theorem
    freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileScaledFiniteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfilePolynomialComparisonToXAxis_of_profileFiniteVolumePolynomial
    (freeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxis_of_scaledFiniteVolumePolynomial
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis
    (freeQ2BoundaryProfileFiniteVolumeComparisonToXAxis_of_profileFiniteVolumePolynomial
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial
    (freeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxis_of_scaledFiniteVolumePolynomial
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfileSubexpComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass _hmass hconn
  rcases hcompare β hβpos hβc with ⟨Aratio, hAratio, hcompareHi⟩
  have hAfkHi : PositiveSubexponentialPrefactor AfkHi :=
    ⟨hconn.2.1, hconn.2.2.2.1⟩
  refine
    ⟨fun n => Aratio n * AfkHi n,
      PositiveSubexponentialPrefactor.mul hAratio hAfkHi, ?_⟩
  filter_upwards [hcompareHi, hAratio.1, hconn.2.2.2.2.2]
    with n hcompare_n hAratio_pos hfkUpper_n
  calc
    freeQ2BoundaryProfileOfBeta β hβpos n
        ≤ Aratio n *
            freeInfiniteVolumeXAxisConnectionOfBetaQ2 β hβpos n :=
      hcompare_n
    _ ≤ Aratio n *
        (AfkHi n * Real.exp (-(mass * (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hfkUpper_n (le_of_lt hAratio_pos)
    _ = (Aratio n * AfkHi n) *
        Real.exp (-(mass * (n : ℝ))) := by
      ring


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_profilePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfilePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profilePolynomialComparisonToXAxis
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumeComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumeComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumeComparisonToXAxis
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_profileFiniteVolumePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfileFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileFiniteVolumePolynomial
      hcompare)


theorem
    freeQ2BoundaryProfileSubexpSameMass_of_profileScaledFiniteVolumePolynomialComparisonToXAxis
    (hcompare :
      FreeQ2BoundaryProfileScaledFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryProfileSubexponentialForFixedInnerSameMassPositiveSubcritical :=
  freeQ2BoundaryProfileSubexpSameMass_of_profileSubexpComparisonToXAxis
    (freeQ2BoundaryProfileSubexpComparisonToXAxis_of_profileScaledFiniteVolumePolynomial
      hcompare)


end Exact3D
end StatMech
