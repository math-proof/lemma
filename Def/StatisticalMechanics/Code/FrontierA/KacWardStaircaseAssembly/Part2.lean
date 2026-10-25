/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly


namespace StatMech.FrontierA

open scoped NNReal

open Set


noncomputable def kwEndpointParameterData
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (M : ℕ) (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 0 < M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1) :
    KWStairParameterData (S := M + 2) polygon where
  parameter i := kwEndpointParameter M beta (alpha (i + 1))
  parameter_zero i := kwEndpointParameter_zero M beta (alpha (i + 1))
  parameter_last i := kwEndpointParameter_last M beta (alpha (i + 1))
  parameter_strict i k := kwEndpointParameter_strict M beta (alpha (i + 1))
    hM hbeta (halpha (i + 1)) (hsum (i + 1)) k

end StatMech.FrontierA
