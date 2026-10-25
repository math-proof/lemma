/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

noncomputable def endpointCountWeight (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable
    ((ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z)
  if (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z then
    x ^ (ofTurns a h0 ts).endpointNumVertices
  else 0


noncomputable def endpointCountObservable (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (x : ℝ) : ℝ :=
  ∑' ts : List ℤ, endpointCountWeight region a h0 z x ts

end
end StatMech.Universality
