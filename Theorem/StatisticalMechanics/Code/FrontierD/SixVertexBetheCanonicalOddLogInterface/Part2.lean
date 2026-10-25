/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogInterface.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits
    {c : Real} (hc : 2 < c) (s : Nat)
    (hbulk : Tendsto (sixVertexCanonicalOddBulkLogDisplacement hc s) atTop
      (nhds (((2 * s + 1 : Nat) : Real) / 2 *
        (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))))
    (hwallis : SixVertexCanonicalOddZeroModeWallisLimit hc s)
    (hboundary : Tendsto (sixVertexCanonicalOddBoundaryLogSum hc s) atTop
      (nhds ((s + 1 : Nat) *
        Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))))) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc
      (2 * s + 1) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hdensity : Tendsto
      (sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s) atTop
      (nhds (-((2 * s + 1 : Nat) : Real) *
        sixVertexAntiferroelectricGapRate lam)) := by
    have hcomb := hwallis.add (hbulk.const_mul 2) |>.sub
      (hboundary.const_mul 2)
    have hdecomp :=
      (eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition
        hc s).mono fun k hk => hk.symm
    have hdensity' := hcomb.congr' hdecomp
    have hvalue :
        Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) +
            2 * (((2 * s + 1 : Nat) : Real) / 2 *
              (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) -
                sixVertexAntiferroelectricGapRate
                  (sixVertexAntiferroelectricLambda c))) -
            2 * ((s + 1 : Nat) *
              Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))) =
          -((2 * s + 1 : Nat) : Real) *
            sixVertexAntiferroelectricGapRate lam := by
      dsimp [lam]
      push_cast
      ring
    rw [hvalue] at hdensity'
    exact hdensity'
  have hcanonical : Tendsto
      (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc
        (2 * s + 1) k) atTop
      (nhds (-((2 * s + 1 : Nat) : Real) *
        sixVertexAntiferroelectricGapRate lam)) :=
    hdensity.congr'
      (eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density hc s).symm
  unfold SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier
  have hpartial := (sixVertexOffsetFourierPartialSum_tendsto
    (sixVertexAntiferroelectricLambda_pos hc)).const_mul
      ((2 * s + 1 : Nat) : Real)
  have hadd := hcanonical.add hpartial
  have hzero :
      -((2 * s + 1 : Nat) : Real) *
          sixVertexAntiferroelectricGapRate lam +
        ((2 * s + 1 : Nat) : Real) *
          sixVertexAntiferroelectricGapRate lam = 0 := by ring
  rw [hzero] at hadd
  simpa [lam] using hadd

end
end StatMech.FrontierD
