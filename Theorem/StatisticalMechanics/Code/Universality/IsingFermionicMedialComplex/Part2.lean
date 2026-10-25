/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part3
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingMedialDart

variable {P : PlanarZ2Subgraph}


theorem localMate_edgeFlip (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) (side : FKIsingMedialSide) :
    localMate (FKIsingDobrushinDomain.localEdgeFlipEquiv e.1 omega) (e, side) =
      match omega e.1, side with
      | false, .west => (e, .north)
      | false, .north => (e, .west)
      | false, .east => (e, .south)
      | false, .south => (e, .east)
      | true, .west => (e, .south)
      | true, .south => (e, .west)
      | true, .east => (e, .north)
      | true, .north => (e, .east) := by
  cases h : omega e.1 <;> cases side <;>
    simp [localMate, FKIsingDobrushinDomain.localEdgeFlipEquiv,
      FKIsingDobrushinDomain.localEdgeFlip, h]


theorem localMate_edgeFlip_of_ne (omega : ConfigSpace (Sym2 P.V))
    (e f : FKIsingMedialVertex P) (hef : f ≠ e)
    (side : FKIsingMedialSide) :
    localMate (FKIsingDobrushinDomain.localEdgeFlipEquiv e.1 omega) (f, side) =
      localMate omega (f, side) := by
  have hne : f.1 ≠ e.1 := by
    intro h
    exact hef (Subtype.ext h)
  cases h : omega f.1 <;> cases side <;>
    simp [localMate, FKIsingDobrushinDomain.localEdgeFlipEquiv,
      FKIsingDobrushinDomain.localEdgeFlip, Function.update_of_ne hne, h]

end FKIsingMedialDart
end
end StatMech.Universality
