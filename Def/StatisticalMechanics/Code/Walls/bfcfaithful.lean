/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfcfaithful.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc67supervertex.Part2
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation


namespace StatMech.Walls

def bff_BoxAllOpen (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ) : Prop :=
  ∀ e ∈ boxEdges 2 n, ω e = true


end StatMech.Walls
