/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCriticalGeneral

open Filter

open WiredBoxSharpness WiredBoxCritical

open WiredBoxLocalized

noncomputable def wiredBeta1Q
    (d : Nat) (q beta0 : Real) : Real :=
  BetaThresholdBound.beta1 (fun b n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b)


noncomputable def betaFKThetaQ
    (d : Nat) (q : Real) (hq : 1 <= q) (beta : Real) : Real :=
  if hbeta : 0 < beta then
    FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q)
  else 0

end WiredBoxCriticalGeneral
end OSSS
end StatMech
