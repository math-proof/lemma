/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryIdentityClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConnFinal
import Def.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part2


namespace StatMech.Universality

open Complex Filter Topology

open scoped Real BigOperators Topology


theorem hbi_witness_identity :
    hexBdryCl * hbi_witness.lam + hexBdryCt * hbi_witness.tau + hbi_witness.ups = 1 :=
  hbi_witness.boundaryIdentity rfl

end StatMech.Universality
