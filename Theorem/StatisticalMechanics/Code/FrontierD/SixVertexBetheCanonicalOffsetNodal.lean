/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetBoundary
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalAbstract
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

theorem sixVertexCanonicalEvenOffsetNodalResidual_eq_weightedConvolution
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin ((s + k + 1) + (s + k + 1))) :
    sixVertexCanonicalEvenOffsetNodalResidual hc s k j =
      2 * Real.pi *
          (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
            ((s + k + 1) + (s + k + 1))
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)
            (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j) *
          sixVertexCanonicalEvenChargeOffset hc s k j) -
        sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
        (1 / (sixVertexFourWidth (2 * s) k : Real)) *
          ∑ l, sixVertexContinuousOffsetKernel c
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k j)
              (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k l) *
            sixVertexCanonicalEvenChargeOffset hc s k l := by
  let N := sixVertexFourWidth (2 * s) k
  let n := (s + k + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalEvenChargeOffset hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s) k).ne'
  unfold sixVertexCanonicalEvenOffsetNodalResidual
  change eps j - sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
    2 * Real.pi * (sixVertexFiniteRootDensity c N n q (q j) * eps j) -
      sixVertexCanonicalEvenOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (q j) (q l) * eps l
  unfold sixVertexContinuousOffsetKernel
  simp_rw [sixVertexRootDensityKernel_div_weight hc]
  unfold sixVertexFiniteRootDensity
  rw [Finset.sum_add_distrib, <- Finset.sum_mul]
  field_simp [hN, Real.pi_ne_zero]
  ring

theorem sixVertexCanonicalOddOffsetNodalResidual_eq_weightedConvolution
    {c : Real} (hc : 2 < c) (s k : Nat)
    (j : Fin (((s + k + 1) + 1) + (s + k + 1))) :
    sixVertexCanonicalOddOffsetNodalResidual hc s k j =
      2 * Real.pi *
          (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k)
            (((s + k + 1) + 1) + (s + k + 1))
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
            (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j) *
          sixVertexCanonicalOddChargeOffset hc s k j) -
        sixVertexCanonicalOddOffsetBoundarySource hc s k j +
        (1 / (sixVertexFourWidth (2 * s + 1) k : Real)) *
          ∑ l, sixVertexContinuousOffsetKernel c
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k j)
              (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k l) *
            sixVertexCanonicalOddChargeOffset hc s k l := by
  let N := sixVertexFourWidth (2 * s + 1) k
  let n := ((s + k + 1) + 1) + (s + k + 1)
  let q := sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k
  let eps := sixVertexCanonicalOddChargeOffset hc s k
  have hN : (N : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  unfold sixVertexCanonicalOddOffsetNodalResidual
  change eps j - sixVertexCanonicalOddOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j +
          (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) /
            sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) =
    2 * Real.pi * (sixVertexFiniteRootDensity c N n q (q j) * eps j) -
      sixVertexCanonicalOddOffsetBoundarySource hc s k j +
      (1 / (N : Real)) * ∑ l,
        sixVertexContinuousOffsetKernel c (q j) (q l) * eps l
  unfold sixVertexContinuousOffsetKernel
  simp_rw [sixVertexRootDensityKernel_div_weight hc]
  unfold sixVertexFiniteRootDensity
  rw [Finset.sum_add_distrib, <- Finset.sum_mul]
  field_simp [hN, Real.pi_ne_zero]
  ring

theorem empiricalContinuousOffsetKernel_le_of_lower
    {c : Real} (hc : 2 < c) {N n r : Nat}
    (hN : 0 < N) (hn : 0 < n) (hcharge : N = 2 * n + 2 * r)
    {p : Fin n -> Real} (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N n p)
    {lower : Real} (hlower : 0 < lower)
    (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N n p y)
    (i : Fin n) :
    (1 / (N : Real)) * ∑ j,
        sixVertexContinuousOffsetKernel c (p i) (p j) /
          sixVertexFiniteRootDensity c N n p (p j) <=
      2 * Real.pi + sixVertexFixedChargeOffsetRowError c N r lower := by
  have hquad := abs_empiricalContinuousOffsetKernel_sub_integral_fixedCharge_pos
    hc hN hn hcharge hopen hsol hlower hdensity (p i)
  have hint : (∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c (p i) y) = 2 * Real.pi := by
    unfold sixVertexContinuousOffsetKernel
    exact intervalIntegral_sixVertexRootDensityKernel_div_weight hc (p i)
  rw [hint] at hquad
  have hle := (le_abs_self
    ((∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
      sixVertexFiniteRootDensity c N n p (p j)) / N - 2 * Real.pi)).trans hquad
  rw [show (1 / (N : Real)) * ∑ j,
      sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N n p (p j) =
      (∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) /
        sixVertexFiniteRootDensity c N n p (p j)) / N by ring]
  linarith

theorem tendsto_sixVertexFixedChargeOffsetRowError_of_lower
    {c lower : Real} (hlower : 0 < lower) (r : Nat) :
    Tendsto (fun k => sixVertexFixedChargeOffsetRowError c
      (sixVertexFourWidth r k) r lower) atTop (nhds 0) := by
  let C := (sixVertexOffsetQuotientLipschitzNNReal c lower 1 0 : Real) *
      sixVertexFiniteRootDensityUniformBound c *
        ((2 * (r : Real) + 1) / lower) * (2 * Real.pi) +
    2 * (r : Real) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) / lower)
  have hwidthNat : Tendsto (sixVertexFourWidth r) atTop atTop :=
    (strictMono_nat_of_lt_succ (fun k => by
      unfold sixVertexFourWidth
      omega)).tendsto_atTop
  have hwidth : Tendsto (fun k : Nat => (sixVertexFourWidth r k : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hwidthNat
  have hzero : Tendsto (fun k : Nat => C / (sixVertexFourWidth r k : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hwidth
  convert hzero using 1
  funext k
  dsimp [C]
  unfold sixVertexFixedChargeOffsetRowError
  field_simp [hlower.ne']

end
end StatMech.FrontierD
