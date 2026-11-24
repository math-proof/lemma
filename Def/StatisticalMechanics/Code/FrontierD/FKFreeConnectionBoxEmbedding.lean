module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
open MeasureTheory SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKFreeConnectionBoxEmbedding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def FKFiniteConnectionEvent (source target : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (FK.openSub G omega).Reachable source target}

end
end StatMech.FrontierD
