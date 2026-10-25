/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def pottsBoundaryProbWired
    (q : Nat) (b : Fin q) (beta J : Real) (x : V) : Real :=
  ∑ sigma : V → Fin q,
    pottsProbWired G bdry q b beta J sigma *
      (if sigma x = b then 1 else 0)

end IsingFK
end StatMech
