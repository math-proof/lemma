/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary.Part2


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

def terminalAdjacentIncidence (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn :=
  Quot.mk _ (leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩)

def terminalAdjacentFace (n : Nat) (hn : 0 < n) :
    FKIsingSquareFullFaceNode n :=
  fkIsingSquareFullFaceOfRadialIncidence n hn
    (terminalAdjacentIncidence n hn)

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
