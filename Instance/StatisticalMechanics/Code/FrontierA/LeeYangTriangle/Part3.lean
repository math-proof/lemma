/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Def.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part4
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


instance finiteTriangleGraphDecidableAdj : (t : ℕ) →
    DecidableRel (finiteTriangleGraph t).Adj
  | 0 => by simp only [finiteTriangleGraph]; infer_instance
  | t + 1 => by
      simp only [finiteTriangleGraph]
      letI := finiteTriangleGraphDecidableAdj t
      infer_instance


end StatMech.FrontierA
