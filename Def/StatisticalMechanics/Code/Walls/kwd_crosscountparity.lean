module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
open Finset Set SimpleGraph
open StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_crosscountparity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

def kwd_crossCount {V : Type*} {G : SimpleGraph V} (B : Sym2 V → Bool)
    {x y : V} (w : G.Walk x y) : ℕ :=
  w.edges.countP B

end StatMech.Walls
