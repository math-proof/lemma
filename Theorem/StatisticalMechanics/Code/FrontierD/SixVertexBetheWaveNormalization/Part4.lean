/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheWaveNormalization.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledBethePhaseCorrectedWaveTwo_packed_pos
    {c : Real} (hc : 2 < c) :
    0 < sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc
      (sixVertexPackedSector 4 2 (by omega)) := by
  let p := sixVertexHalfFilledBetheRoots hc 0
  have hp : 0 < p 1 := by
    simpa [p, sixVertexPositiveHalfBetheRoots] using
      sixVertexPositiveHalfBetheRoots_pos hc 0 (0 : Fin 1)
  have hpPi : p 1 < Real.pi := by
    simpa [p, sixVertexPositiveHalfBetheRoots] using
      sixVertexPositiveHalfBetheRoots_lt_pi hc 0 (0 : Fin 1)
  have hsin : 0 < Real.sin (p 1) := Real.sin_pos_of_pos_of_lt_pi hp hpPi
  unfold sixVertexHalfFilledBethePhaseCorrectedWaveTwo
    sixVertexHalfFilledBetheRotatedRealWave
  change 0 < ((-Complex.I) * sixVertexCoordinateBetheWave (N := 4) c p
    (sixVertexPackedSector 4 2 (by omega))).re
  rw [sixVertexCoordinateBetheWave_two_packed_eq_phase_sub
    (c := c) (p := p) (sixVertexHalfFilledBetheRoots_mem_open hc 0).2.1]
  have hsymm := (sixVertexHalfFilledBetheRoots_mem_open hc 0).2.1
    (0 : Fin 2)
  have hp10 : p 1 = -p 0 := by simpa [p] using hsymm
  have hp01 : p 0 = -p 1 := by linarith
  simp [sixVertexBethePhase, Complex.exp_im, hp01, Real.sin_neg]
  linarith


theorem sixVertexHalfFilledBethePhaseCorrectedWaveTwo_eigenrelation
    {c : Real} (hc : 2 < c) :
    sixVertexSectorTransfer 4 2 c *ᵥ
        sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc =
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc 0) •
        sixVertexHalfFilledBethePhaseCorrectedWaveTwo hc := by
  exact sixVertexHalfFilledBetheRotatedRealWave_eigenrelation hc 0 (-Complex.I)

end
end StatMech.FrontierD
