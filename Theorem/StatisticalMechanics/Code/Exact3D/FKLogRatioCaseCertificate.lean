/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part3


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem exactMonomialFKMass_congr_predictedExponent
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent) :
    exactMonomialFKMass C = exactMonomialFKMass D := by
  funext p
  simp [exactMonomialFKMass, hpred]

set_option linter.style.longLine false in


theorem logRatioValue_exactMonomialFKMass
    (C : RGCertificate Ising3DModel)
    {p : ℝ}
    (hp : p ∈ Set.Ioo (Ising3DFKPC - (1 : ℝ) / 2) Ising3DFKPC) :
    logRatioValue (exactMonomialFKMass C) p =
      C.predictedExponent := by
  have hdpos : 0 < Ising3DFKPC - p := sub_pos.mpr hp.2
  have hdlt_half : Ising3DFKPC - p < (1 : ℝ) / 2 := by
    linarith [hp.1]
  have hdlt_one : Ising3DFKPC - p < 1 := by
    linarith
  have hlog_neg : Real.log (Ising3DFKPC - p) < 0 :=
    (Real.log_neg_iff hdpos).mpr hdlt_one
  have hlog_ne : Real.log (Ising3DFKPC - p) ≠ 0 := ne_of_lt hlog_neg
  calc
    logRatioValue (exactMonomialFKMass C) p
        = (C.predictedExponent * Real.log (Ising3DFKPC - p)) /
            Real.log (Ising3DFKPC - p) := by
          simp [logRatioValue, exactMonomialFKMass]
    _ = C.predictedExponent := by
          field_simp [hlog_ne]

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
