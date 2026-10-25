/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


def twoVertexEdge : SimpleGraph (Fin 2) := ⊤

end StatMech.FrontierA
