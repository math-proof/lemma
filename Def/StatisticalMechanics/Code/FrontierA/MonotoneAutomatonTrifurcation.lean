/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part3


namespace StatMech.FrontierA

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.Percolation

open StatMech.Walls


variable {V : Type*} [Fintype V] [Nonempty V]


def forestBranchVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => 3 ≤ G.degree v


def forestLeaves (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => G.degree v = 1

end StatMech.FrontierA
