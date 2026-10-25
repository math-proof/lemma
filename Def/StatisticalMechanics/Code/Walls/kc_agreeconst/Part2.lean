/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_agreeconst.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.kc_agreeconst
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section EdgeBoundary

variable {V : Type*} {G : SimpleGraph V} (S : Set V)


variable (G) in


def edgeBoundary : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ crossesBoundary S e}


end EdgeBoundary
end StatMech.Walls
