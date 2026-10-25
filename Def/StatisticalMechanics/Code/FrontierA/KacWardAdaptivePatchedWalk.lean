/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple
import Structure.StatisticalMechanics.Code.FrontierA.KacWardAdaptivePatchedWalk


namespace StatMech.FrontierA

open Set

noncomputable def kwAdaptivePatchedData
    {n M : ℕ} [NeZero n] [NeZero M] (polygon : KWFiniteSimplePolygon n)
    (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 2 ≤ M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1)
    (hconnector : ∀ i : Fin n, Nonempty (KWAdaptiveConnectorData
      (alpha i * (-polygon.edgeVector (i - 1)))
      (beta * polygon.edgeVector i))) :
    KWAdaptivePatchedData (M := M) polygon where
  data := kwEndpointParameterData polygon M beta alpha (by omega) hbeta halpha hsum
  beta := beta
  alpha := alpha
  hM := hM
  hbeta := hbeta
  halpha := halpha
  hsum := hsum
  parameter_one := kwEndpointParameterData_parameter_one
    polygon beta alpha (by omega) hbeta halpha hsum
  parameter_penultimate := kwEndpointParameterData_parameter_penultimate
    polygon beta alpha (by omega) hbeta halpha hsum
  connector i := (hconnector i).some

noncomputable def KWAdaptivePatchedData.incomingPort
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : ℂ :=
  patch.data.base i (Fin.last (M + 1)).castSucc

noncomputable def KWAdaptivePatchedData.outgoingPort
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : ℂ :=
  patch.data.base i (0 : Fin (M + 2)).succ

noncomputable def KWAdaptivePatchedData.connectorCorner
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : ℂ :=
  polygon.vertex i + (patch.connector i).corner

noncomputable def KWAdaptivePatchedData.pathBase
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (k : Fin (M + 1)) : ℂ :=
  Fin.lastCases (patch.incomingPort i)
    (fun q : Fin M ↦ patch.data.base i q.succ.castSucc.castSucc) k


def KWAdaptivePatchedData.connectorUsesVerticalFirst
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) : Prop :=
  (patch.connector i).corner = kwVHConnectorCorner
    (patch.alpha i * (-polygon.edgeVector (i - 1)))
    (patch.beta * polygon.edgeVector i)

end StatMech.FrontierA
