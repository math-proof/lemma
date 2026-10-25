/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingDobrushinMedialComplex

variable {P : PlanarZ2Subgraph} (C : FKIsingDobrushinMedialComplex P)


@[simp] theorem winding_west (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .west) = C.baseWinding omega e := by
  simp [winding, FKIsingMedialSide.angle]

theorem winding_east (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .east) = C.winding omega (e, .west) + Real.pi := by
  simp [winding, FKIsingMedialSide.angle]

theorem winding_south (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .south) =
      C.winding omega (e, .west) - Real.pi / 2 := by
  simp [winding, FKIsingMedialSide.angle]
  ring

theorem winding_north (omega : ConfigSpace (Sym2 P.V))
    (e : FKIsingMedialVertex P) :
    C.winding omega (e, .north) =
      C.winding omega (e, .west) + Real.pi / 2 := by
  simp [winding, FKIsingMedialSide.angle]


end FKIsingDobrushinMedialComplex
end
end StatMech.Universality
