/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/FvES.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


def ConnToBdry (ω : ConfigSpace (Sym2 V)) (x : V) : Prop :=
  ∃ y, bdry y ∧ Connected G ω x y

end IsingFK
end StatMech
