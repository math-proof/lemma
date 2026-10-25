/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part6
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abgrOffWeight (J : Sym2 V -> Real) (beta : Real)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) : Real :=
  ∏ e : {e // e ∉ FieldGhostDict.ghostEdges V},
    if eta e then pBeta (abfaLiftCoupling G J e) beta
    else 1 - pBeta (abfaLiftCoupling G J e) beta

end Sharpness
end StatMech
