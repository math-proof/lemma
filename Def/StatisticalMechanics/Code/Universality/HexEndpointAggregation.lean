/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hexEndpointSAWwt
    (a : ℂ) (h0 : ℤ) (x : ℝ) (ts : List ℤ) : ℝ :=
  haveI := Classical.propDecidable (ofTurns a h0 ts).EndpointIsLegalSAW
  if (ofTurns a h0 ts).EndpointIsLegalSAW then
    x ^ (ofTurns a h0 ts).endpointNumVertices
  else 0

end
end StatMech.Universality
