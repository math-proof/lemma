/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.IsingFK.BetacPc.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence
open Real Set


namespace StatMech

namespace IsingFK

noncomputable def pottsFKMagnetization (d : ℕ) (q : ℝ) (hq : 1 < q) (beta : ℝ) : ℝ :=
  if hbeta : 0 < beta then
    FK.fkTheta d
      (by
        rw [← betaToP_zero q]
        exact (strictMono_betaToP q hq) hbeta)
      (betaToP_mem q beta hq hbeta.le).2
      (zero_lt_one.trans hq) (q := q)
  else 0


end IsingFK
end StatMech
