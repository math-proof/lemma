/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangSingleEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangDisjointUnion
import Def.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


instance : DecidableRel twoVertexEdge.Adj := by
  unfold twoVertexEdge
  infer_instance


end StatMech.FrontierA
