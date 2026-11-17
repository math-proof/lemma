/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic

@[expose] public section

namespace StatMech.Lattice

open SimpleGraph

variable {V : Type*}


def cyclomaticNumber (G : SimpleGraph V) [Fintype V] [Fintype G.edgeSet] : ℕ :=
  (G.edgeFinset.card + 1) - Fintype.card V


end StatMech.Lattice
