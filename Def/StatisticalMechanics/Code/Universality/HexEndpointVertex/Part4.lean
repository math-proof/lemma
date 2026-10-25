/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part3


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

noncomputable def endpointParafSummand (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x : ℝ) (ts : List ℤ) : ℂ :=
  haveI := Classical.propDecidable
    ((ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z then
    Complex.exp (-Complex.I * (σ : ℂ) * ((ofTurns a h0 ts).turning : ℂ)) *
      ((x : ℂ) ^ (ofTurns a h0 ts).endpointNumVertices)
  else 0


noncomputable def endpointParafObservable (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x : ℝ) : ℂ :=
  ∑' ts : List ℤ, endpointParafSummand region a h0 z σ x ts


noncomputable def endpointCombinedSummand (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) (ts : List ℤ) : ℂ :=
  ((v + du) - v) *
      endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts +
    ((v + hexOmega * du) - v) *
      endpointParafSummand region a h0 (v + hexOmega * du)
        (5 / 8) hexChi ts +
    ((v + hexOmega ^ 2 * du) - v) *
      endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
        (5 / 8) hexChi ts


end
end StatMech.Universality
