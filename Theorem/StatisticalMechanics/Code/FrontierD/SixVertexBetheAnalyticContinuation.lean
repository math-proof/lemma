/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronAnalytic.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem analyticOnNhd_sixVertexHalfFilledPerronNormalized (k : Nat) :
    AnalyticOnNhd Real (sixVertexHalfFilledPerronNormalized k) (Set.Ioi 2) := by
  intro c hc
  change 2 < c at hc
  let N := sixVertexFourWidth 0 k
  let n := (k + 1) + (k + 1)
  have hn : n ≤ N := by
    dsimp [n, N, sixVertexFourWidth]
    omega
  have htop : AnalyticAt Real (sixVertexSectorTopEigenvalue N n hn) c :=
    analyticAt_sixVertexSectorTopEigenvalue hn (by linarith)
  have hscale : AnalyticAt Real
      (fun t : Real => (t ^ 2 - 2) ^ n) c := by fun_prop
  have hscale_ne : (c ^ 2 - 2) ^ n ≠ 0 := by
    apply pow_ne_zero
    nlinarith
  simpa [sixVertexHalfFilledPerronNormalized, N, n] using
    htop.div hscale hscale_ne


end
end StatMech.FrontierD
