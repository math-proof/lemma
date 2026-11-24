module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
public import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part4
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

section EvenSubgraphDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

theorem compF_le (F : Finset (Sym2 V)) (f : V) : compF F f ≤ subgraphF F := fun _ _ h => h.1

end EvenSubgraphDecomp
end Ising
end StatMech
