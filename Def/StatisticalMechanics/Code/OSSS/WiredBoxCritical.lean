/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxSharpness
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCritical

open Filter

open WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


noncomputable def wiredBeta1 (d : Nat) (beta0 : Real) : Real :=
  BetaThresholdBound.beta1 (fun b n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n b)


noncomputable def betaFKTheta (d : Nat) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2)
  else 0

end WiredBoxCritical
end OSSS
end StatMech
