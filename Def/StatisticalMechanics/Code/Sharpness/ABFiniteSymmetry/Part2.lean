/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFiniteSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteSymmetry
open Finset Set SimpleGraph


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def abfsOptionEquiv (sigma : V ≃ V) : Option V ≃ Option V := sigma.optionCongr


def abfsEdgeEquiv (sigma : V ≃ V) :
    Sym2 (Option V) ≃ Sym2 (Option V) :=
  StatMech.Lattice.sym2Congr (abfsOptionEquiv sigma)

end Sharpness
end StatMech
