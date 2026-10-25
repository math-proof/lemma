/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Instance.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part4
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


theorem finiteSmallComponentGraph_hasLeeYangCircle (i e t : ℕ) {beta : ℝ}
    (hbeta : 0 ≤ beta) : HasLeeYangCircle (finiteSmallComponentGraph i e t) beta := by
  unfold finiteSmallComponentGraph
  apply HasLeeYangCircle.sum
  · intro z hz
    exact leeYangComplexPolynomial_bot_root_norm beta hz
  · exact HasLeeYangCircle.sum (finiteMatching e) (finiteTriangleGraph t)
      (finiteMatching_hasLeeYangCircle e hbeta)
      (finiteTriangleGraph_hasLeeYangCircle t hbeta)

end StatMech.FrontierA
