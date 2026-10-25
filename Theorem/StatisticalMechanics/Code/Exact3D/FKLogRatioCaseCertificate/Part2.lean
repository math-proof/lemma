/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part4


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem constantPrefactorMonomialFKMass_congr_predictedExponent
    (C D : RGCertificate Ising3DModel)
    (A : ℝ)
    (hpred : C.predictedExponent = D.predictedExponent) :
    constantPrefactorMonomialFKMass C A =
      constantPrefactorMonomialFKMass D A := by
  funext p
  simp [constantPrefactorMonomialFKMass,
    exactMonomialFKMass_congr_predictedExponent C D hpred]

set_option linter.style.longLine false in


theorem logRatioValue_constantPrefactorMonomialFKMass
    (C : RGCertificate Ising3DModel)
    {A p : ℝ}
    (hA : 0 < A)
    (hp : p ∈ Set.Ioo (Ising3DFKPC - (1 : ℝ) / 2) Ising3DFKPC) :
    logRatioValue (constantPrefactorMonomialFKMass C A) p =
      C.predictedExponent + Real.log A / Real.log (Ising3DFKPC - p) := by
  have hdpos : 0 < Ising3DFKPC - p := sub_pos.mpr hp.2
  have hdlt_half : Ising3DFKPC - p < (1 : ℝ) / 2 := by
    linarith [hp.1]
  have hdlt_one : Ising3DFKPC - p < 1 := by
    linarith
  have hlog_neg : Real.log (Ising3DFKPC - p) < 0 :=
    (Real.log_neg_iff hdpos).mpr hdlt_one
  have hlog_ne : Real.log (Ising3DFKPC - p) ≠ 0 := ne_of_lt hlog_neg
  have hA_ne : A ≠ 0 := hA.ne'
  have hexp_ne :
      Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) ≠ 0 :=
    (Real.exp_pos _).ne'
  calc
    logRatioValue (constantPrefactorMonomialFKMass C A) p
        = (Real.log A +
              C.predictedExponent * Real.log (Ising3DFKPC - p)) /
            Real.log (Ising3DFKPC - p) := by
          unfold logRatioValue constantPrefactorMonomialFKMass exactMonomialFKMass
          rw [Real.log_mul hA_ne hexp_ne, Real.log_exp]
    _ = C.predictedExponent + Real.log A / Real.log (Ising3DFKPC - p) := by
          field_simp [hlog_ne]
          ring

set_option linter.style.longLine false in


theorem eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack
    (C : RGCertificate Ising3DModel)
    {A ε : ℝ}
    (hA : 0 < A)
    (hε : 0 < ε) :
    ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
      C.predictedExponent - ε / 2 <
          logRatioValue (constantPrefactorMonomialFKMass C A) p ∧
        logRatioValue (constantPrefactorMonomialFKMass C A) p <
          C.predictedExponent + ε / 2 := by
  let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
  have hhalf : 0 < ε / 2 := by positivity
  have hlogd :
      Filter.Tendsto (fun p : ℝ => Real.log (Ising3DFKPC - p)) L
        Filter.atBot := by
    simpa [L, ParameterModel] using
      tendsto_log_betaC_sub_atBot (ParameterModel Ising3DFKPC)
  have hconst :
      Filter.Tendsto
        (fun p : ℝ => Real.log A / Real.log (Ising3DFKPC - p))
        L (nhds 0) :=
    hlogd.const_div_atBot (Real.log A)
  have hdist := (Metric.tendsto_nhds.mp hconst) (ε / 2) hhalf
  filter_upwards
    [hdist,
      Ioo_mem_nhdsLT
        (show Ising3DFKPC - (1 : ℝ) / 2 < Ising3DFKPC by norm_num)]
    with p hpdist hpwindow
  rw [Real.dist_eq] at hpdist
  have hsmall : |Real.log A / Real.log (Ising3DFKPC - p)| < ε / 2 := by
    simpa using hpdist
  have hvalue := logRatioValue_constantPrefactorMonomialFKMass C hA hpwindow
  rw [hvalue]
  have hsmall_bounds := abs_lt.mp hsmall
  constructor <;> linarith

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
