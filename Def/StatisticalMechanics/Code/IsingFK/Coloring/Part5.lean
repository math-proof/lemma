/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part4
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in

def openCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = true)).card


def closedCount (ω : ConfigSpace (Sym2 V)) : ℕ :=
  (G.edgeFinset.filter (fun e => ω e = false)).card

end IsingFK
end StatMech
