module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
public import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWDualBijection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

section Transport

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def transportEdges (e : V ≃ W) (F : Finset (Sym2 V)) : Finset (Sym2 W) :=
  F.image (Sym2.map e)

end Transport
end Ising
end StatMech
