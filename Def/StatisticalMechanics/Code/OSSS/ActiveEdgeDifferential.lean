/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCovLowerGeom
import Theorem.StatisticalMechanics.Code.OSSS.RussoPrefactor
import Theorem.StatisticalMechanics.Code.OSSS.ActiveEdgeDifferential
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace ActiveEdgeDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open RevealmentTranslation

open LindebergTree

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {d : ℕ}

noncomputable def incidentEdges {E : Type*} [Fintype E]
    (endU endV : E → Site d) (o : Site d) : Finset E :=
  Finset.univ.filter (fun e => endU e = o ∨ endV e = o)

end ActiveEdgeDifferential
end OSSS
end StatMech
