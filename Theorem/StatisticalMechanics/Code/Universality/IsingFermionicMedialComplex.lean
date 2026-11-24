module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalSwitching.Part12
public import Theorem.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part2
open Finset SimpleGraph
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMedialComplex.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice

noncomputable section

namespace FKIsingMedialDart

variable {P : PlanarZ2Subgraph}


theorem localMate_involutive (omega : ConfigSpace (Sym2 P.V)) :
    Function.Involutive (localMate omega) := by
  rintro ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;> simp [localMate, h]

theorem localMate_ne (omega : ConfigSpace (Sym2 P.V))
    (d : FKIsingMedialDart P) : localMate omega d ≠ d := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;> simp [localMate, h]

end FKIsingMedialDart
end
end StatMech.Universality
