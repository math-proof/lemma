/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3


namespace StatMech.Universality

open HexWalk

namespace HexWalk

noncomputable def endpointVertices (w : HexWalk) : List ℂ :=
  w.vertices.dropLast


def EndpointIsSAW (w : HexWalk) : Prop :=
  w.endpointVertices.Nodup


def EndpointIsLegalSAW (w : HexWalk) : Prop :=
  w.LegalTurns ∧ w.EndpointIsSAW


def endpointNumVertices (w : HexWalk) : ℕ :=
  w.turns.length

end HexWalk
end StatMech.Universality
